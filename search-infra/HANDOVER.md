# 探索基盤（LRATパイプライン）引き継ぎメモ — 2026-11-27 時点

Muse（この VM 上の別エージェント）が `~/workspace/pequalnp-muse/` 以下に作ったもの。
Claude Code 側のクローンには触っていない。作業ルール: セッション開始時に upstream を fetch して
main を fast-forward のみで追随し、build する（ローカル main に自前コミットは載せない）。

## 環境

- クローン: `~/workspace/pequalnp-muse/pequalnp-proofs`（origin = mizuchin のフォーク、upstream = open-goat/pequalnp-proofs）
- Lean toolchain leanprover/lean4:v4.36.0、Mathlib キャッシュ取得済み。`tools/pnp.sh` は gh 前提（ログイン済み）
- CaDiCaL 2.2.1: `~/workspace/pequalnp-muse/bin/cadical`
- 提出制約: 1 PR = 新規ファイル1つ `lean/PEqualNP/Outside/L_<gap>.lean`、512 KiB 以下、宣言文はデスクの文面どおり、sorry・新公理・native_decide・文字列リテラル・`#` コマンド禁止

## 完了済み

### M1: 既存 LRAT ファイルの再現（手元の完了条件 = 再生成一致 + lake build 通過）
- 対象 L_meta_2229（n=5, s=4, 辺 03,04,12,13,14）: mkrow の rows がマージ済みファイルと完全一致。
  生成側の `lower` は宣言文より強い（ReadsBack 仮定なし）ので、仮定を捨てるだけで宣言文に一致
- 公式チェッカーの最終判定はこの VM では完走しない（検証器のカーネル再検査が30分で終わらない）。
  ユーザー決定により、最終判定は提出時にプロジェクト側チェッカーへ委ねる

### M2: 小規模性能表（`search-infra/perf/perf.csv`、22設定）
- cycle グラフ C_n（n=4〜9、s=3〜6）と K23 アンカーで測定
- C4 は全て SAT（cycle は因数分解するので UNSAT の族として貧弱）
- CaDiCaL は全設定 0.54 秒以下（ソルバは律速にならない）
- 512 KiB 制限は s=6 から噛む（s≤5 は最大約 355 KB、s=6 は約 1.9〜2.2 MB で約4倍超）
- Lean ビルドが律速（s=6 で約225秒）。C9_9_6 はこの VM で OOM kill（証明書自体は正常）

### M3: 分類器 + A 型の完全自動化
- `search-infra/classify.py`: 宣言文テキストから A/B/C を規則ベースで判定。マージ済み5件で検証済み
  （2229→A、5531→B の正確サイズ型、3644→C、10000/10002→C の被覆系）
- `search-infra/importer.py`: genrow/mkrow 出力（Library.LRAT.Link を import）を、Checker.lean +
  Link.lean を `PEqualNP.Outside.<gap>_aux` 名前空間へ取り込んだ自己完結ファイルに変換。
  ビルドテスト通過（2229 で 146,002 bytes、lake build exit 0）
- `search-infra/pipeline.py`: 入力は gap id と宣言文テキストのみ。分類A → パラメータ抽出 →
  mkrow → 取り込み → 整形 → 512 KiB 検査 → lake build。統合テスト通過（2229、148,304 bytes、build exit 0）
  → **A 型ステップは宣言文を渡すだけで提出ファイルまで作れる**

### M4 調査: B は3亜種（`search-infra/m4-survey.md`）
- **B-promise**（RepSizeAtMost / マスク型）: ライブラリほぼ完備。Promise.lean は Link2 の `enc2`
  （= Defs の enc + fLex、単調・NOT 無し）を使う。接続点は `rep_lower_mask (n m M s)` で、
  必要なのは `¬ FormulaSat (enc2 (n+m) s (gMask n m M) (repRows n m))`
- **B-readcount**（lineDegrees による読み取り回数上限）: ライブラリ支援なし。例 L_meta_1388 の証明構造の読解から
- **B-firstgate**: 名前で引ける実例は未発見。デスクの実例待ち

### M4 promise: CNF 生成器の検証通過
- `search-infra/genpromise.py`: `enc2 (n+m) s (gMask n m M) (repRows n m)` の CNF を生成。
  Lean 本体の #eval 出力と **341節すべて順序込みで完全一致**を検証済み（n=2, m=2, M=11, s=2）
- 配線部品も作成済み: `search-infra/genpromiserow.py`（promise 用の行ファイル生成器。検査対象の
  公式は Lean の enc2 自体で、CNF は証明書ヒントの読み取り専用）、`search-infra/mkpromiserow.py`
  （(n, m, M, s) → genpromise → CaDiCaL → genpromiserow のワンコマンド）

## 未完了・次の手

1. promise の通しテスト: mkpromiserow の出力に `rep_lower_mask` の最終定理を付けて lake build まで（未実施）
2. 分類器に RepSizeAtMost / マスク型の (n, m, M, s) 抽出を追加し、pipeline の B-promise 分岐を生やす
3. B-readcount: L_meta_1388 のマージ済み証明の構造を読むところから
4. M5（方向4）: L_meta_5531 型（下限は LRAT、上限は回路の明示）の一般化で1件通す案

## 作業記録

- 計画と進捗ログ: `search-infra/PLAN.md`、調査メモ: `search-infra/m4-survey.md`、
  取り込み器の設計メモ: `search-infra/importer-design.md`
