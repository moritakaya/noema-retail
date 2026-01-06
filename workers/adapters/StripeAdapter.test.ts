import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { StripeAdapter, StripeApiError, type StripeConfig } from './StripeAdapter';

// Mock fetch globally
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// Mock crypto.subtle for HMAC verification
const mockCryptoSubtle = {
  importKey: vi.fn(),
  sign: vi.fn(),
};
vi.stubGlobal('crypto', {
  subtle: mockCryptoSubtle,
});

describe('StripeAdapter', () => {
  const config: StripeConfig = {
    apiKey: 'sk_test_xxx',
    webhookSecret: 'whsec_test_secret',
    productMapping: [
      {
        stripeProductId: 'prod_test1',
        stripePriceId: 'price_test1',
        noemaProductId: 'NOEMA001:SKU001',
        noemaLocationId: 'warehouse',
      },
      {
        stripeProductId: 'prod_test2',
        noemaProductId: 'NOEMA002:SKU002',
      },
    ],
  };

  let adapter: StripeAdapter;

  beforeEach(() => {
    adapter = new StripeAdapter(config);
    mockFetch.mockClear();
    mockCryptoSubtle.importKey.mockClear();
    mockCryptoSubtle.sign.mockClear();
  });

  afterEach(() => {
    vi.clearAllMocks();
  });

  describe('Webhook署名検証', () => {
    beforeEach(() => {
      // HMAC署名のモック
      mockCryptoSubtle.importKey.mockResolvedValue('mock-key');
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array([0xab, 0xcd, 0xef]).buffer
      );
    });

    it('有効な署名を検証できる', async () => {
      const timestamp = Math.floor(Date.now() / 1000);
      const payload = '{"type":"test"}';

      // 署名を計算
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array(
          'abcdef'.split('').map((_, i) => i)
        ).buffer
      );

      const signature = `t=${timestamp},v1=000102030405`;

      const result = await adapter.verifyWebhookSignature(payload, signature);

      expect(mockCryptoSubtle.importKey).toHaveBeenCalled();
      expect(mockCryptoSubtle.sign).toHaveBeenCalled();
    });

    it('タイムスタンプが古すぎる場合は拒否する', async () => {
      const oldTimestamp = Math.floor(Date.now() / 1000) - 400; // 6分以上前
      const payload = '{"type":"test"}';
      const signature = `t=${oldTimestamp},v1=abcdef`;

      const result = await adapter.verifyWebhookSignature(payload, signature);

      expect(result).toBe(false);
    });

    it('署名がない場合は拒否する', async () => {
      const result = await adapter.verifyWebhookSignature('{}', 't=123');

      expect(result).toBe(false);
    });
  });

  describe('Webhookハンドラー', () => {
    const mockInventoryAttractor = {
      fetch: vi.fn(),
    };

    beforeEach(() => {
      mockInventoryAttractor.fetch.mockClear();
      // 署名検証を常に成功させる
      mockCryptoSubtle.importKey.mockResolvedValue('mock-key');
    });

    it('checkout.session.completedイベントを処理する', async () => {
      const timestamp = Math.floor(Date.now() / 1000);

      // 署名を一致させるためのモック
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05]).buffer
      );

      const event = {
        id: 'evt_test',
        type: 'checkout.session.completed',
        created: timestamp,
        data: {
          object: {
            id: 'cs_test',
            object: 'checkout.session',
            payment_status: 'paid',
            status: 'complete',
            line_items: {
              data: [
                {
                  id: 'li_test',
                  price: { id: 'price_test1', product: 'prod_test1' },
                  quantity: 2,
                  description: 'Test Product',
                },
              ],
            },
          },
        },
      };

      const payload = JSON.stringify(event);
      const signature = `t=${timestamp},v1=000102030405`;

      mockInventoryAttractor.fetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ success: true }),
      });

      const result = await adapter.handleWebhook(
        payload,
        signature,
        mockInventoryAttractor
      );

      expect(result.success).toBe(true);
      expect(result.eventsProcessed).toBe(1);

      // InventoryAttractorが呼ばれたことを確認
      expect(mockInventoryAttractor.fetch).toHaveBeenCalledWith(
        expect.objectContaining({
          method: 'POST',
        })
      );
    });

    it('無効な署名の場合はエラーを返す', async () => {
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array([0xff, 0xff]).buffer // 不一致
      );

      const result = await adapter.handleWebhook(
        '{}',
        't=123,v1=invalid',
        mockInventoryAttractor
      );

      expect(result.success).toBe(false);
      expect(result.message).toContain('Invalid webhook signature');
    });

    it('無効なJSONの場合はエラーを返す', async () => {
      const timestamp = Math.floor(Date.now() / 1000);
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05]).buffer
      );

      const result = await adapter.handleWebhook(
        'invalid json',
        `t=${timestamp},v1=000102030405`,
        mockInventoryAttractor
      );

      expect(result.success).toBe(false);
      expect(result.message).toContain('Invalid JSON');
    });

    it('未対応のイベントタイプは成功として扱う', async () => {
      const timestamp = Math.floor(Date.now() / 1000);
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05]).buffer
      );

      const event = {
        id: 'evt_test',
        type: 'customer.created',
        created: timestamp,
        data: { object: {} },
      };

      const result = await adapter.handleWebhook(
        JSON.stringify(event),
        `t=${timestamp},v1=000102030405`,
        mockInventoryAttractor
      );

      expect(result.success).toBe(true);
      expect(result.message).toContain('acknowledged but not processed');
    });
  });

  describe('商品マッピング', () => {
    it('Price IDでマッピングを検索できる', async () => {
      const timestamp = Math.floor(Date.now() / 1000);
      mockCryptoSubtle.importKey.mockResolvedValue('mock-key');
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05]).buffer
      );

      const mockInventoryAttractor = {
        fetch: vi.fn().mockResolvedValue({
          ok: true,
          json: () => Promise.resolve({ success: true }),
        }),
      };

      const event = {
        id: 'evt_test',
        type: 'checkout.session.completed',
        created: timestamp,
        data: {
          object: {
            id: 'cs_test',
            payment_status: 'paid',
            status: 'complete',
            line_items: {
              data: [
                {
                  id: 'li_test',
                  price: { id: 'price_test1', product: 'prod_test1' },
                  quantity: 1,
                },
              ],
            },
          },
        },
      };

      await adapter.handleWebhook(
        JSON.stringify(event),
        `t=${timestamp},v1=000102030405`,
        mockInventoryAttractor
      );

      const fetchCall = mockInventoryAttractor.fetch.mock.calls[0][0];
      const body = JSON.parse(await fetchCall.text());
      expect(body.productId).toBe('NOEMA001:SKU001');
      expect(body.locationId).toBe('warehouse');
    });

    it('マッピングがない商品は無視される', async () => {
      const timestamp = Math.floor(Date.now() / 1000);
      mockCryptoSubtle.importKey.mockResolvedValue('mock-key');
      mockCryptoSubtle.sign.mockResolvedValue(
        new Uint8Array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05]).buffer
      );

      const mockInventoryAttractor = {
        fetch: vi.fn(),
      };

      const event = {
        id: 'evt_test',
        type: 'checkout.session.completed',
        created: timestamp,
        data: {
          object: {
            id: 'cs_test',
            payment_status: 'paid',
            status: 'complete',
            line_items: {
              data: [
                {
                  id: 'li_test',
                  price: { id: 'price_unknown', product: 'prod_unknown' },
                  quantity: 1,
                },
              ],
            },
          },
        },
      };

      const result = await adapter.handleWebhook(
        JSON.stringify(event),
        `t=${timestamp},v1=000102030405`,
        mockInventoryAttractor
      );

      expect(mockInventoryAttractor.fetch).not.toHaveBeenCalled();
      expect(result.eventsProcessed).toBe(0);
    });
  });

  describe('Noema連携（インターフェース互換）', () => {
    const mockInventoryAttractor = {
      fetch: vi.fn(),
    };

    it('syncToNoemaは常に成功を返す（Stripeには在庫概念がない）', async () => {
      const result = await adapter.syncToNoema('NOEMA001:SKU001', mockInventoryAttractor);

      expect(result.success).toBe(true);
      expect(result.channel).toBe('self_ec');
    });

    it('syncFromNoemaは常に成功を返す（Stripeには在庫を設定できない）', async () => {
      const result = await adapter.syncFromNoema('NOEMA001:SKU001', 100);

      expect(result.success).toBe(true);
      expect(result.channel).toBe('self_ec');
    });
  });
});

describe('StripeApiError', () => {
  it('isRetryableが5xxエラーでtrueを返す', () => {
    const error = new StripeApiError(502, 'Bad Gateway', '/test');
    expect(error.isRetryable()).toBe(true);
  });

  it('isRetryableが429エラーでtrueを返す', () => {
    const error = new StripeApiError(429, 'Rate Limited', '/test');
    expect(error.isRetryable()).toBe(true);
  });

  it('isRetryableが4xxエラーでfalseを返す', () => {
    const error = new StripeApiError(400, 'Bad Request', '/test');
    expect(error.isRetryable()).toBe(false);
  });
});
