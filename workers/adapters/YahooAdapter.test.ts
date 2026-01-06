import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { YahooAdapter, YahooApiError, type YahooConfig } from './YahooAdapter';

// Mock fetch globally
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('YahooAdapter', () => {
  const config: YahooConfig = {
    sellerId: 'test-seller',
    clientId: 'test-client-id',
    clientSecret: 'test-client-secret',
    refreshToken: 'test-refresh-token',
    publicKey: 'test-public-key',
    publicKeyVersion: 1,
    publicKeyExpiry: Date.now() + 86400000,
  };

  let adapter: YahooAdapter;

  beforeEach(() => {
    adapter = new YahooAdapter(config);
    mockFetch.mockClear();
  });

  afterEach(() => {
    vi.clearAllMocks();
  });

  describe('OAuth2認証', () => {
    it('アクセストークンを取得してリクエストに使用する', async () => {
      // トークン取得
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          access_token: 'new-access-token',
          token_type: 'Bearer',
          expires_in: 3600,
        }),
      });

      // 在庫取得API
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: {
            totalResultsAvailable: 1,
            totalResultsReturned: 1,
            firstResultPosition: 1,
            Result: [{ ItemCode: 'TEST001', Quantity: 100 }],
          },
        }),
      });

      await adapter.getStock('TEST001:default');

      // トークン取得リクエストの検証
      expect(mockFetch).toHaveBeenNthCalledWith(
        1,
        expect.stringContaining('auth.login.yahoo.co.jp'),
        expect.objectContaining({
          method: 'POST',
          body: expect.stringContaining('grant_type=refresh_token'),
        })
      );

      // 在庫APIリクエストの検証
      expect(mockFetch).toHaveBeenNthCalledWith(
        2,
        expect.stringContaining('/ShoppingWebService/V1/getStock'),
        expect.objectContaining({
          headers: expect.objectContaining({
            Authorization: 'Bearer new-access-token',
          }),
        })
      );
    });

    it('キャッシュされたトークンを再利用する', async () => {
      // 初回トークン取得
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          access_token: 'cached-token',
          token_type: 'Bearer',
          expires_in: 3600,
        }),
      });

      // 初回API呼び出し
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: { Result: [{ ItemCode: 'TEST001', Quantity: 100 }] },
        }),
      });

      await adapter.getStock('TEST001:default');

      // 2回目API呼び出し（トークン再利用）
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: { Result: [{ ItemCode: 'TEST002', Quantity: 50 }] },
        }),
      });

      await adapter.getStock('TEST002:default');

      // トークン取得は1回のみ
      const tokenCalls = mockFetch.mock.calls.filter(call =>
        call[0].includes('auth.login.yahoo.co.jp')
      );
      expect(tokenCalls).toHaveLength(1);
    });
  });

  describe('在庫取得', () => {
    beforeEach(() => {
      // トークン取得をモック
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          access_token: 'test-token',
          token_type: 'Bearer',
          expires_in: 3600,
        }),
      });
    });

    it('getStockが正常に在庫を取得する', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: {
            totalResultsAvailable: 1,
            Result: [{ ItemCode: 'TEST001', SubCode: 'RED', Quantity: 100 }],
          },
        }),
      });

      const result = await adapter.getStock('TEST001:RED');

      expect(result).toMatchObject({
        ItemCode: 'TEST001',
        SubCode: 'RED',
        Quantity: 100,
      });
    });

    it('存在しない商品の場合、nullを返す', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: {
            totalResultsAvailable: 0,
            Result: [],
          },
        }),
      });

      const result = await adapter.getStock('NOTEXIST:default');

      expect(result).toBeNull();
    });
  });

  describe('在庫更新', () => {
    beforeEach(() => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          access_token: 'test-token',
          token_type: 'Bearer',
          expires_in: 3600,
        }),
      });
    });

    it('setStockが正常に在庫を更新する', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: {
            Status: 'OK',
            Result: [{ ItemCode: 'TEST001', Quantity: 50 }],
          },
        }),
      });

      await adapter.setStock('TEST001:RED', 50);

      const setStockCall = mockFetch.mock.calls.find(call =>
        call[0].includes('/setStock')
      );
      expect(setStockCall).toBeDefined();
      expect(setStockCall[1].body).toContain('quantity=50');
    });

    it('adjustStockが差分を計算して更新する', async () => {
      // getStock
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: { Result: [{ ItemCode: 'TEST001', Quantity: 100 }] },
        }),
      });

      // setStock
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: { Status: 'OK', Result: [] },
        }),
      });

      await adapter.adjustStock('TEST001:default', -30, '販売');

      const setStockCall = mockFetch.mock.calls.find(call =>
        call[0].includes('/setStock')
      );
      expect(setStockCall[1].body).toContain('quantity=70'); // 100 - 30
    });
  });

  describe('Noema連携', () => {
    const mockInventoryAttractor = {
      fetch: vi.fn(),
    };

    beforeEach(() => {
      mockInventoryAttractor.fetch.mockClear();
      // トークン取得
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          access_token: 'test-token',
          token_type: 'Bearer',
          expires_in: 3600,
        }),
      });
    });

    it('syncToNoemaが正常に同期する', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: { Result: [{ ItemCode: 'TEST001', Quantity: 100 }] },
        }),
      });

      mockInventoryAttractor.fetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ success: true }),
      });

      const result = await adapter.syncToNoema('TEST001:default', mockInventoryAttractor);

      expect(result.success).toBe(true);
      expect(result.channel).toBe('yahoo');
      expect(result.quantitySynced).toBe(100);
    });

    it('syncFromNoemaが正常に同期する', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        headers: new Map([['content-type', 'application/json']]),
        json: () => Promise.resolve({
          ResultSet: { Status: 'OK', Result: [] },
        }),
      });

      const result = await adapter.syncFromNoema('TEST001:default', 80);

      expect(result.success).toBe(true);
      expect(result.quantitySynced).toBe(80);
    });
  });

  describe('注文処理', () => {
    it('orderToInventoryEventsが注文をイベントに変換する', () => {
      const order = {
        OrderId: 'ORDER001',
        OrderTime: '2025-01-06T10:00:00+09:00',
        OrderStatus: 'confirmed',
        Item: [
          {
            ItemId: 'ITEM001',
            Title: 'テスト商品',
            SubCode: 'RED',
            Quantity: 3,
            UnitPrice: 1500,
          },
        ],
      };

      const events = adapter.orderToInventoryEvents(order);

      expect(events).toHaveLength(1);
      expect(events[0]).toMatchObject({
        eventType: 'sale',
        productId: 'ITEM001:RED',
        channel: 'yahoo',
        delta: -3,
        referenceId: 'ORDER001',
      });
    });
  });

  describe('公開鍵管理', () => {
    it('有効期限切れを検出する', () => {
      const expiredAdapter = new YahooAdapter({
        ...config,
        publicKeyExpiry: Date.now() - 1000,
      });
      expect(expiredAdapter.isPublicKeyExpired()).toBe(true);
    });

    it('有効期限内を検出する', () => {
      expect(adapter.isPublicKeyExpired()).toBe(false);
    });
  });
});

describe('YahooApiError', () => {
  it('isRetryableが5xxエラーでtrueを返す', () => {
    const error = new YahooApiError(503, 'Service Unavailable', '/test');
    expect(error.isRetryable()).toBe(true);
  });

  it('isRetryableが429エラーでtrueを返す', () => {
    const error = new YahooApiError(429, 'Too Many Requests', '/test');
    expect(error.isRetryable()).toBe(true);
  });

  it('isRetryableが4xxエラーでfalseを返す', () => {
    const error = new YahooApiError(401, 'Unauthorized', '/test');
    expect(error.isRetryable()).toBe(false);
  });
});
