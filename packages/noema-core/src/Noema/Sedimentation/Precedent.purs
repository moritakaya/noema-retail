-- | Noema Sedimentation: Precedent（判例）
-- |
-- | Connection 検証に失敗した Intent を「判例」として記録する。
-- | 将来の Nomos 改訂に影響を与える重要な情報源。
-- |
-- | ## 圏論的位置づけ
-- |
-- | Precedent は「失敗した射」の記録。
-- | Intent 圏における射 A → B が Cognition で解釈できなかった場合、
-- | その失敗パターンを Precedent として沈殿させる。
-- |
-- | ## 哲学的基盤
-- |
-- | Precedent（先例、判例）は法システムにおける重要な概念。
-- | 過去の判断が将来の判断を拘束する。
-- |
-- | Noema においては：
-- | - Connection 検証で Curved/Critical と判定された Intent を記録
-- | - 同じパターンの Intent が繰り返し棄却される場合、Nomos 改訂の契機となる
-- | - 「なぜこの Intent が棄却されたか」の履歴を保持
-- |
-- | ## 使用シナリオ
-- |
-- | 1. **Intent 棄却時**:
-- |    - stagingId で保留中の Intent を識別
-- |    - rejectionReason に Curved/Critical の理由を記録
-- |
-- | 2. **Nomos 改訂検討時**:
-- |    - 頻出する rejectionReason を分析
-- |    - 附則の例外規則追加を検討
-- |
-- | 3. **監査・コンプライアンス**:
-- |    - 法令遵守の証跡として保持
-- |    - originalIntent で元の意図を追跡
module Noema.Sedimentation.Precedent
  ( -- * PrecedentRecord
    PrecedentRecord
  , mkPrecedentRecord
    -- * PrecedentLog
  , PrecedentLog
  , emptyPrecedentLog
  , addPrecedent
  , findPrecedents
  , precedentCount
    -- * 判例に基づく Connection 検証
  , verifyConnectionWithPrecedent
  ) where

import Prelude

import Data.Array as Array
import Data.Argonaut.Core (Json)
import Noema.Topos.Situs (Timestamp(..))
import Noema.Topos.Nomos (NomosVersion, World, Reason, ConnectionType(..), verifyConnection)

-- ============================================================
-- PrecedentRecord（判例記録）
-- ============================================================

-- | 判例記録
-- |
-- | Connection 検証で棄却された Intent の記録。
-- |
-- | ## フィールド
-- |
-- | - stagingId: StagingArea での保留 ID
-- | - nomosVersion: 棄却時の Nomos バージョン
-- | - rejectionReason: 棄却理由（Curved/Critical の Reason）
-- | - rejectedAt: 棄却時刻
-- | - originalIntent: 元の Intent（JSON シリアライズ）
-- | - world: 棄却時の World（法座標）
-- |
-- | ## 設計ノート
-- |
-- | originalIntent を Json として保持するのは：
-- | - Intent の型が Vocabulary によって異なるため
-- | - 将来の分析・再評価のために構造を保存
type PrecedentRecord =
  { stagingId :: String
  , nomosVersion :: NomosVersion
  , rejectionReason :: Reason
  , rejectedAt :: Timestamp
  , originalIntent :: Json
  , world :: World
  }

-- | PrecedentRecord を作成
mkPrecedentRecord
  :: String       -- ^ stagingId
  -> NomosVersion -- ^ nomosVersion
  -> Reason       -- ^ rejectionReason
  -> Timestamp    -- ^ rejectedAt
  -> Json         -- ^ originalIntent
  -> World        -- ^ world
  -> PrecedentRecord
mkPrecedentRecord sid nv reason ts intent world =
  { stagingId: sid
  , nomosVersion: nv
  , rejectionReason: reason
  , rejectedAt: ts
  , originalIntent: intent
  , world: world
  }

-- ============================================================
-- PrecedentLog（判例ログ）
-- ============================================================

-- | 判例ログ
-- |
-- | 棄却された Intent の履歴。
-- | Subject（Attractor）ごとに保持される。
-- |
-- | ## 運用ノート
-- |
-- | - records は新しい順（先頭が最新）
-- | - 古い判例は定期的にアーカイブ（実装は Attractor に委任）
-- | - lastUpdated は最後に判例が追加された時刻
type PrecedentLog =
  { records :: Array PrecedentRecord
  , lastUpdated :: Timestamp
  }

-- | 空の PrecedentLog を作成
emptyPrecedentLog :: PrecedentLog
emptyPrecedentLog =
  { records: []
  , lastUpdated: Timestamp 0.0
  }

-- | 判例を追加
-- |
-- | 新しい判例を先頭に追加し、lastUpdated を更新。
addPrecedent :: PrecedentRecord -> PrecedentLog -> PrecedentLog
addPrecedent record log =
  { records: Array.cons record log.records
  , lastUpdated: record.rejectedAt
  }

-- | 条件に合致する判例を検索
-- |
-- | 指定された Reason を含む判例を返す。
findPrecedents :: Reason -> PrecedentLog -> Array PrecedentRecord
findPrecedents reason log =
  Array.filter (\r -> r.rejectionReason == reason) log.records

-- | 判例の総数
precedentCount :: PrecedentLog -> Int
precedentCount log = Array.length log.records

-- ============================================================
-- 判例に基づく Connection 検証
-- ============================================================

-- | 判例を考慮した Connection 検証
-- |
-- | 基本の verifyConnection に加えて、過去の判例を参照。
-- |
-- | ## 判定ロジック
-- |
-- | 1. 基本の Connection 検証を実行
-- | 2. Flat の場合でも、同一パターンの棄却判例が存在すれば警告
-- | 3. 過去 N 回以上同じ理由で棄却されていれば Critical に昇格
-- |
-- | ## 設計ノート
-- |
-- | 現在の実装は簡易版。将来は：
-- | - 判例のパターンマッチング強化
-- | - 機械学習による棄却予測
-- | - Lean4 による形式検証との統合
verifyConnectionWithPrecedent
  :: PrecedentLog
  -> World
  -> World
  -> ConnectionType
verifyConnectionWithPrecedent plog origin target =
  let
    baseConnection = verifyConnection origin target

    -- 同一バージョン間の棄却判例を検索
    relatedPrecedents = Array.filter
      (\r -> r.nomosVersion == origin.nomosVersion)
      plog.records

    -- 棄却回数による昇格判定
    precedentThreshold = 3
  in
    case baseConnection of
      Flat
        | Array.length relatedPrecedents >= precedentThreshold ->
            Curved "Multiple precedents suggest caution"
        | otherwise ->
            Flat
      Curved reason
        | Array.length relatedPrecedents >= precedentThreshold ->
            Critical ("Recurring issue: " <> reason)
        | otherwise ->
            Curved reason
      Critical reason ->
        Critical reason
