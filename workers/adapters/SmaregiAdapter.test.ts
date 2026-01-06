import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { SmaregiAdapter, SmaregiApiError, type SmaregiConfig } from './SmaregiAdapter';

// Mock fetch globally
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('SmaregiAdapter', () => {
  const config: SmaregiConfig = {
    contractId: 'test-contract',
    clientId: 'test-client-id',
    clientSecret: 'test-client-secret',
    accessToken: 'test-access-token',
    refreshToken: 'test-refresh-token',
    storeId: 'store001',
    apiBaseUrl: 'https://api.smaregi.dev',
  };

  let adapter: SmaregiAdapter;

  beforeEach(() => {
    adapter = new SmaregiAdapter(config);
    mockFetch.mockClear();
  });

  afterEach(() => {
    vi.clearAllMocks();
  });

  describe('認証', () => {
    it('Bearer認証ヘッダーが正しく設定される', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ products: [] }),
      });

      await adapter.getProducts();

      expect(mockFetch).toHaveBeenCalledWith(
        expect.any(String),
        expect.objectContaining({
          headers: expect.objectContaining({
            Authorization: `Bearer ${config.accessToken}`,
          }),
        })
      );
    });

    it('APIベースURLとコントラクトIDが正しく構成される', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ products: [] }),
      });

      await adapter.getProducts();

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining(`${config.apiBaseUrl}/${config.contractId}`),
        expect.any(Object)
      );
    });
  });

  describe('商品取得', () => {
    it('getProductsが商品一覧を取得する', async () => {
      const mockProducts = [
        { productId: 'P001', productCode: 'SKU001', productName: 'テスト商品1', price: 1000, stockQuantity: 10 },
        { productId: 'P002', productCode: 'SKU002', productName: 'テスト商品2', price: 2000, stockQuantity: 20 },
      ];

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ products: mockProducts }),
      });

      const result = await adapter.getProducts({ limit: 10, page: 1 });

      expect(result).toEqual(mockProducts);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('/pos/products?'),
        expect.any(Object)
      );
    });

    it('getProductが単一商品を取得する', async () => {
      const mockProduct = {
        productId: 'P001',
        productCode: 'SKU001',
        productName: 'テスト商品',
        price: 1000,
        stockQuantity: 10,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockProduct),
      });

      const result = await adapter.getProduct('P001');

      expect(result).toEqual(mockProduct);
    });

    it('存在しない商品の場合、nullを返す', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 404,
        text: () => Promise.resolve('Not found'),
      });

      const result = await adapter.getProduct('NOTEXIST');

      expect(result).toBeNull();
    });
  });

  describe('在庫取得', () => {
    it('getStockが在庫を取得する', async () => {
      const mockStock = {
        productId: 'P001',
        storeId: 'store001',
        stockQuantity: 100,
        stockAmount: 100000,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ stocks: [mockStock] }),
      });

      const result = await adapter.getStock('P001');

      expect(result).toEqual(mockStock);
    });

    it('在庫が存在しない場合、nullを返す', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ stocks: [] }),
      });

      const result = await adapter.getStock('NOTEXIST');

      expect(result).toBeNull();
    });

    it('getStocksが在庫一覧を取得する', async () => {
      const mockStocks = [
        { productId: 'P001', storeId: 'store001', stockQuantity: 100, stockAmount: 100000 },
        { productId: 'P002', storeId: 'store001', stockQuantity: 50, stockAmount: 50000 },
      ];

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ stocks: mockStocks }),
      });

      const result = await adapter.getStocks({ limit: 10 });

      expect(result).toEqual(mockStocks);
    });
  });

  describe('在庫調整', () => {
    it('在庫減少時に出荷登録を呼び出す', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({}),
      });

      await adapter.adjustStock('P001', -10, '販売による在庫減');

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('/pos/stock/shipment'),
        expect.objectContaining({
          method: 'POST',
          body: expect.stringContaining('"quantity":10'),
        })
      );
    });

    it('在庫増加時に入荷登録を呼び出す', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({}),
      });

      await adapter.adjustStock('P001', 20, '入荷');

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('/pos/stock/receipt'),
        expect.objectContaining({
          method: 'POST',
          body: expect.stringContaining('"quantity":20'),
        })
      );
    });

    it('delta=0の場合、何も呼び出さない', async () => {
      await adapter.adjustStock('P001', 0, 'no change');

      expect(mockFetch).not.toHaveBeenCalled();
    });
  });

  describe('取引処理', () => {
    it('getTransactionsが取引一覧を取得する', async () => {
      const mockTransactions = [
        {
          transactionHeadId: 'TXN001',
          transactionDateTime: '2025-01-06T10:00:00+09:00',
          storeId: 'store001',
          terminalId: 'term001',
          total: 3000,
          details: [
            { productId: 'P001', productCode: 'SKU001', productName: '商品1', quantity: 2, price: 1000, subtotal: 2000 },
          ],
        },
      ];

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ transactions: mockTransactions }),
      });

      const result = await adapter.getTransactions({
        from: new Date('2025-01-01'),
        to: new Date('2025-01-06'),
      });

      expect(result).toEqual(mockTransactions);
    });

    it('transactionToInventoryEventsが取引をイベントに変換する', () => {
      const transaction = {
        transactionHeadId: 'TXN001',
        transactionDateTime: '2025-01-06T10:00:00+09:00',
        storeId: 'store001',
        terminalId: 'term001',
        total: 3000,
        details: [
          { productId: 'P001', productCode: 'SKU001', productName: '商品1', quantity: 2, price: 1000, subtotal: 2000 },
          { productId: 'P002', productCode: 'SKU002', productName: '商品2', quantity: 1, price: 1000, subtotal: 1000 },
        ],
      };

      const events = adapter.transactionToInventoryEvents(transaction);

      expect(events).toHaveLength(2);
      expect(events[0]).toMatchObject({
        eventType: 'sale',
        productId: 'P001',
        locationId: 'smaregi_store_store001',
        channel: 'smaregi',
        delta: -2,
        referenceId: 'TXN001',
      });
      expect(events[1]).toMatchObject({
        eventType: 'sale',
        productId: 'P002',
        delta: -1,
      });
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
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          stocks: [{ productId: 'P001', storeId: 'store001', stockQuantity: 100, stockAmount: 100000 }],
        }),
      });

      mockInventoryAttractor.fetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ success: true }),
      });

      const result = await adapter.syncToNoema('P001', mockInventoryAttractor);

      expect(result.success).toBe(true);
      expect(result.channel).toBe('smaregi');
      expect(result.quantitySynced).toBe(100);
    });

    it('商品が見つからない場合、エラーを返す', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ stocks: [] }),
      });

      const result = await adapter.syncToNoema('NOTEXIST', mockInventoryAttractor);

      expect(result.success).toBe(false);
      expect(result.error).toContain('not found');
    });

    it('syncFromNoemaが正常に同期する', async () => {
      // getStock
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          stocks: [{ productId: 'P001', storeId: 'store001', stockQuantity: 80, stockAmount: 80000 }],
        }),
      });

      // adjustStock (receipt)
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({}),
      });

      const result = await adapter.syncFromNoema('P001', 100);

      expect(result.success).toBe(true);
      expect(result.quantitySynced).toBe(100);

      // 差分20の入荷登録が呼ばれたことを確認
      expect(mockFetch).toHaveBeenNthCalledWith(
        2,
        expect.stringContaining('/pos/stock/receipt'),
        expect.any(Object)
      );
    });

    it('processNewTransactionsが取引を処理する', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          transactions: [
            {
              transactionHeadId: 'TXN001',
              transactionDateTime: '2025-01-06T10:00:00+09:00',
              storeId: 'store001',
              terminalId: 'term001',
              total: 1000,
              details: [
                { productId: 'P001', productCode: 'SKU001', productName: '商品1', quantity: 1, price: 1000, subtotal: 1000 },
              ],
            },
          ],
        }),
      });

      mockInventoryAttractor.fetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({ success: true }),
      });

      const result = await adapter.processNewTransactions(
        new Date('2025-01-06T00:00:00'),
        mockInventoryAttractor
      );

      expect(result.processed).toBe(1);
      expect(result.errors).toHaveLength(0);
    });
  });
});

describe('SmaregiApiError', () => {
  it('statusCodeとmessageが正しく設定される', () => {
    const error = new SmaregiApiError(500, 'Internal Server Error');

    expect(error.statusCode).toBe(500);
    expect(error.message).toBe('Internal Server Error');
    expect(error.name).toBe('SmaregiApiError');
  });
});
