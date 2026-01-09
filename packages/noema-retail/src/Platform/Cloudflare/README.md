# Platform/Cloudflare

## 役割

Cloudflare Workers および Durable Objects のバインディングと Attractor 実装を提供する。
Noema の圏論的構造を Cloudflare の分散インフラ上に実現する。

## 圏論的位置づけ

```
Sedimentation/Factum
    │
    ↓ collapse（忘却）
Platform/Cloudflare/
├── Attractor（A-algebra）
│   ├── InventoryAttractor.purs  # 在庫管理
│   └── SubjectAttractor.purs    # 主体管理
└── FFI/（外界との境界）
```

| 概念 | 圏論 | 実装 |
|------|------|------|
| **Attractor** | A-algebra | Durable Object |
| **Sediment** | 代数への作用 | SQLite INSERT |
| **collapse** | 忘却 | Factum → Effect |

## 主要コンポーネント

### Attractor（Durable Objects）

- `InventoryAttractor.purs`: 在庫管理の DO
  - REST API: GET/POST /inventory, /adjust, /reserve
  - SQLite Storage で状態管理

- `SubjectAttractor.purs`: 主体管理の DO
  - REST API: GET/POST/PATCH /subject
  - Subject の CRUD 操作

### FFI（Workers API バインディング）

- `DurableObject.purs`: DO State, Storage API
- `Request.purs`: HTTP Request
- `Response.purs`: HTTP Response
- `SqlStorage.purs`: SQLite Storage API
- `Fetch.purs`: 外部 API 呼び出し
- `Crypto.purs`: 暗号化操作

### Router

- `Router.purs`: HTTP ルーティング（Hono ベース）

## Attractor パターン

```purescript
-- Attractor の状態
type AttractorState =
  { env :: Env           -- Interpretation 環境
  , storage :: Storage   -- DO Storage
  , initialized :: Bool
  }

-- HTTP リクエスト処理
handleFetch :: AttractorState -> Request -> Effect Response
handleFetch state req = do
  state' <- ensureInitialized state
  -- Intent を構築
  let intent = buildIntent req
  -- Factum として実行、collapse で Effect へ
  collapse do
    result <- runIntent state'.env intent unit
    recognize $ jsonResponse result

-- アラーム処理
handleAlarm :: AttractorState -> Effect Unit
handleAlarm state = do
  -- 定期処理（クリーンアップ等）
  pure unit
```

## Factum と Effect の境界

Attractor のエントリーポイントは外界との境界。
内部では Factum を使用し、collapse で Effect に変換。

```purescript
handleGetInventory :: State -> ThingId -> SubjectId -> Effect Response
handleGetInventory state tid sid = collapse do
  -- Factum 内で Intent を実行
  let intent = getStock tid sid
  result <- runInventoryIntent state.env intent unit
  -- Response 作成も Factum 内
  recognize $ jsonResponse result
```

## 使用例

```purescript
import Platform.Cloudflare.InventoryAttractor (createAttractor, handleFetch)
import Platform.Cloudflare.FFI.DurableObject (DurableObjectState)

-- Worker エントリーポイント
fetch :: DurableObjectState -> Request -> Effect Response
fetch ctx req = do
  state <- createAttractor ctx
  handleFetch state req
```

## 他のモジュールとの関係

```
noema-core                         noema-retail
───────────────────────────────────────────────────
Cognition/Interpretation.purs
        │
        ↓
                              Cognition/
                              ├── InventoryInterpretation.purs
                              └── SubjectInterpretation.purs
                                      │
                                      ↓
                              Platform/Cloudflare/
                              ├── InventoryAttractor.purs
                              ├── SubjectAttractor.purs
                              ├── Router.purs
                              └── FFI/
```

## wrangler.json 設定例

```json
{
  "durable_objects": {
    "bindings": [
      {
        "name": "INVENTORY_ATTRACTOR",
        "class_name": "InventoryAttractor"
      },
      {
        "name": "SUBJECT_ATTRACTOR",
        "class_name": "SubjectAttractor"
      }
    ]
  },
  "migrations": [
    {
      "tag": "v1",
      "new_sqlite_classes": ["InventoryAttractor", "SubjectAttractor"]
    }
  ]
}
```
