import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { RakutenAdapter, RakutenApiError, type RakutenConfig } from './RakutenAdapter';

// Mock fetch globally
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('RakutenAdapter', () => {
  let config: RakutenConfig;
  let adapter: RakutenAdapter;

  beforeEach(() => {
    config = {
      shopUrl: 'test-shop',
      serviceSecret: 'SP3_test_secret',
      licenseKey: 'SL3_test_license',
      licenseExpiry: Date.now() + 30 * 24 * 60 * 60 * 1000, // 30日後
    };
    adapter = new RakutenAdapter(config);
    mockFetch.mockClear();
  });

  afterEach(() => {
    vi.clearAllMocks();
  });

  describe('認証', () => {
    it('ESA認証ヘッダーが正しく生成される', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ quantity: 10, manageNumber: 'TEST001', variantId: 'SKU001' }),
      });

      await adapter.getStock('TEST001:SKU001');

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('/es/2.0/inventories/'),
        expect.objectContaining({
          headers: expect.objectContaining({
            Authorization: expect.stringMatching(/^ESA /),
          }),
        })
      );

      // Base64エンコードの検証
      const call = mockFetch.mock.calls[0];
      const authHeader = call[1].headers.Authorization;
      const encoded = authHeader.replace('ESA ', '');
      const decoded = atob(encoded);
      expect(decoded).toBe(`${config.serviceSecret}:${config.licenseKey}`);
    });
  });

  describe('ライセンスキー管理', () => {
    it('有効期限内の場合、isLicenseExpiredがfalseを返す', () => {
      expect(adapter.isLicenseExpired()).toBe(false);
    });

    it('有効期限切れの場合、isLicenseExpiredがtrueを返す', () => {
      const expiredAdapter = new RakutenAdapter({
        ...config,
        licenseExpiry: Date.now() - 1000, // 過去
      });
      expect(expiredAdapter.isLicenseExpired()).toBe(true);
    });

    it('期限切れ間近の場合、警告メッセージを返す', () => {
      const soonExpireAdapter = new RakutenAdapter({
        ...config,
        licenseExpiry: Date.now() + 7 * 24 * 60 * 60 * 1000, // 7日後
      });
      const warning = soonExpireAdapter.getLicenseExpiryWarning();
      expect(warning).toContain('expires in');
      expect(warning).toContain('days');
    });

    it('十分な期限がある場合、nullを返す', () => {
      const warning = adapter.getLicenseExpiryWarning();
      expect(warning).toBeNull();
    });
  });

  describe('在庫取得', () => {
    it('getStockが正常に在庫を取得する', async () => {
      const mockResponse = {
        manageNumber: 'TEST001',
        variantId: 'SKU001',
        quantity: 100,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const result = await adapter.getStock('TEST001:SKU001');

      expect(result).toEqual(mockResponse);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('/es/2.0/inventories/manage-numbers/TEST001/variants/SKU001'),
        expect.any(Object)
      );
    });

    it('存在しない商品の場合、nullを返す', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 404,
        text: () => Promise.resolve('Not found'),
      });

      const result = await adapter.getStock('NOTEXIST:SKU');

      expect(result).toBeNull();
    });

    it('APIエラーの場合、RakutenApiErrorをスローする', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        text: () => Promise.resolve('Internal Server Error'),
      });

      await expect(adapter.getStock('TEST001:SKU001')).rejects.toThrow(RakutenApiError);
    });
  });

  describe('在庫更新', () => {
    it('updateStocksが正常に在庫を更新する', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({}),
      });

      await adapter.updateStocks([
        { manageNumber: 'TEST001', variantId: 'SKU001', quantity: 50 },
      ]);

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('/es/2.0/inventories/bulk-upsert'),
        expect.objectContaining({
          method: 'POST',
          body: expect.stringContaining('"mode":"ABSOLUTE"'),
        })
      );
    });

    it('adjustStockが差分を計算して更新する', async () => {
      // getStock のモック
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ manageNumber: 'TEST001', variantId: 'SKU001', quantity: 100 }),
      });
      // updateStocks のモック
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({}),
      });

      await adapter.adjustStock('TEST001:SKU001', -10, 'テスト調整');

      // 2回目の呼び出し（updateStocks）を検証
      const updateCall = mockFetch.mock.calls[1];
      const body = JSON.parse(updateCall[1].body);
      expect(body.inventories[0].quantity).toBe(90); // 100 - 10
    });

    it('在庫不足の場合、エラーをスローする', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ manageNumber: 'TEST001', variantId: 'SKU001', quantity: 5 }),
      });

      await expect(adapter.adjustStock('TEST001:SKU001', -10, 'テスト')).rejects.toThrow(
        'Insufficient stock'
      );
    });
  });

  describe('Noema連携', () => {
    const mockInventoryAttractor = {
      fetch: vi.fn(),
    };

    beforeEach(() => {
      mockInventoryAttractor.fetch.mockClear();
    });

    it('syncToNoemaが正常に同期する', async () => {
      // 楽天API応答
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ manageNumber: 'TEST001', variantId: 'SKU001', quantity: 100 }),
      });

      // InventoryAttractor応答
      mockInventoryAttractor.fetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ success: true }),
      });

      const result = await adapter.syncToNoema('TEST001:SKU001', mockInventoryAttractor);

      expect(result.success).toBe(true);
      expect(result.channel).toBe('rakuten');
      expect(result.quantitySynced).toBe(100);
    });

    it('ライセンス期限切れの場合、エラーを返す', async () => {
      const expiredAdapter = new RakutenAdapter({
        ...config,
        licenseExpiry: Date.now() - 1000,
      });

      const result = await expiredAdapter.syncToNoema('TEST001:SKU001', mockInventoryAttractor);

      expect(result.success).toBe(false);
      expect(result.error).toContain('expired');
    });

    it('syncFromNoemaが正常に同期する', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({}),
      });

      const result = await adapter.syncFromNoema('TEST001:SKU001', 50);

      expect(result.success).toBe(true);
      expect(result.quantitySynced).toBe(50);
    });
  });

  describe('注文処理', () => {
    it('orderToInventoryEventsが注文をイベントに変換する', () => {
      const order = {
        orderNumber: 'ORDER001',
        orderDatetime: '2025-01-06T10:00:00+09:00',
        orderStatus: 'confirmed',
        orderProgress: 100,
        PackageModelList: [
          {
            basketId: 1,
            ItemModelList: [
              {
                itemNumber: 'ITEM001',
                manageNumber: 'TEST001',
                itemName: 'テスト商品',
                units: 2,
                price: 1000,
                selectedChoice: 'RED',
              },
            ],
          },
        ],
      };

      const events = adapter.orderToInventoryEvents(order);

      expect(events).toHaveLength(1);
      expect(events[0]).toMatchObject({
        eventType: 'sale',
        productId: 'TEST001:RED',
        channel: 'rakuten',
        delta: -2,
        referenceId: 'ORDER001',
      });
    });
  });
});

describe('RakutenApiError', () => {
  it('isRetryableが5xxエラーでtrueを返す', () => {
    const error = new RakutenApiError(500, 'Internal Server Error', '/test');
    expect(error.isRetryable()).toBe(true);
  });

  it('isRetryableが429エラーでtrueを返す', () => {
    const error = new RakutenApiError(429, 'Too Many Requests', '/test');
    expect(error.isRetryable()).toBe(true);
  });

  it('isRetryableが4xxエラーでfalseを返す', () => {
    const error = new RakutenApiError(400, 'Bad Request', '/test');
    expect(error.isRetryable()).toBe(false);
  });
});
