# マイルストーン4（B のつなぎ補題）下調べメモ（2026-11-26）

## ライブラリの既存資産（lean/PEqualNP/Library/LRAT/）
Checker / Cube / Link / Link2 / LinkN / LinkN2 / Promise / PromiseCube / PromiseGen。

## B の内訳は一様ではない（重要）
### B-promise（RepSizeAtMost・マスク型）— ライブラリ完備に近い
- Promise.lean: `promise_lower`（rows による約束つき下界の一般形）、4×4 専用の
  `rep_lower44`、`lit_lower4`。
- PromiseGen.lean: n×m 一般化。`rep_lower`、`rep_lower_mask`（マスク M から
  関数 g を作る形）。最近フィードに大量に出る 4×4 マスクステップはこの系統。
- 残作業: 宣言文 → (n, m, M, s) の読み取りと、約束版 CNF の生成器の確認
  （genmono は通常の enc 用。約束版が notes 側にあるか要確認）。
- L_meta_5531（正確サイズ型）の下半分もこの近傍。

### B-readcount（読み取り回数）— ライブラリ支援なし
- 実例 L_meta_1388: `¬∃ Ckt, ... (Ckt.lineDegrees ...).getD ... ≤ 2 ∧ ...` の形。
  回路の各ラインの読み取り回数を lineDegrees で縛る宣言文。
- firstGate 系の名前はライブラリに無い。符号化への織り込みから要る本命の難所。

### B-firstgate（最初のゲート固定）
- 名前での実例は未発見。デスクの実ステップの宣言文サンプルが要る。

### 範囲外の注意
- L_meta_164 の CoverPromise は頂点被覆の別系統（MetaComplexity 側）で、
  LRAT パイプラインの B ではない。分類器では C のままが正しい。

## 進め方
1. B-promise から: PromiseGen の rows と CNF 生成の対応を確認し、
   分類器に RepSizeAtMost パターンの詳細（n, m, M, s 抽出）を足す。
2. B-readcount は L_meta_1388 の証明構造（どう解かれたか）を先に読む。
3. 方向4（M5）は L_meta_5531 型（正確サイズ）の一般化として扱える可能性。

## 追記（2026-11-26 21:31）: promise 型の接続点が確定
- `rep_lower_mask (n m M s)` の前提は `¬ FormulaSat (enc2 (n+m) s (gMask n m M) (repRows n m))`。
  rows は単位行 2^u + 2^(n+v) の全体（repRows）、g は rows 上で M.testBit (m*u+v)。
- よって B-promise の実作業は「enc2（Defs.LratEncoding）＋任意の rows と g」に対応する
  CNF 生成器 `genpromise.py` の作成が中心。genmono は enc 専用、genrow は --enc2 対応済み。
- 未確認: Promise 側が使う enc2 が Link2（単調・対称性除去）か LinkN（NOT）か、
  NOT 版の promise 定理が存在するか。gennot.py の対応先と合わせて次回確認する。

## B-readcount: L_meta_1388 の証明構造（2026-11-27 読解）

- 130 KB、import は Mathlib + PEqualNP.Defs のみ。LRAT/SAT 符号化は一切使っていない
- 中身は手書きの組合せ論法: LMeta616（ゲート除去・単純化エンジン: step/statVal/simpMono/elimPass）、
  cubicBound（3正則グラフの頂点被覆に関する一般の下界定理）、WireComponents.coloring、
  FanoPartition.partition_bound、Diagonal.split、FanoProduct.impossible/endpoint
  （7+7 の Fano 平面の数え上げ）を組み立てて最終定理（lineDegrees ≤ 2 の ¬∃ 主張）に接続
- 結論: この族は符号化の問題ではない。自動化するなら除去論法そのもののインスタンス別形式化が
  要り、パイプライン化の対象ではなく研究レベルの作業。優先度を下げ、実例が増えるまで保留が妥当
