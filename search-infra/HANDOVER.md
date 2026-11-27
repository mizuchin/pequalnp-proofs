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
- `search-infra/importer.py`（v2、書式ガード対応済み）: genrow/mkrow 出力（Library.LRAT.Link を
  import）を、Checker.lean + Link.lean を `PEqualNP.Outside.<gap>_aux` 名前空間へ取り込んだ
  自己完結ファイルに変換。ガード（outside-guard.mjs はコメント含む生テキストを走査）への対応:
  ライブラリ部分のコメント全除去、`macro "wdt"` を削除し使用13件を展開形に置換、import は
  `PEqualNP.Defs` のみ（MetaComplexityLgpMono は Defs ルート配下）、Shannon は Defs ルート外なので
  wire-fold 補題6件を aux 名前空間へコピー（L_meta_3644 と同じやり方）、open から Helpers を除去
- `search-infra/pipeline.py`: 入力は gap id と宣言文テキストのみ。分類A → パラメータ抽出 →
  mkrow → 取り込み → 整形 → 512 KiB 検査 → **書式ガード3コマンド（gap-of-file / imports /
  closure）** → lake build。再検証通過（2026-11-27、2229 で 137,262 bytes、GUARD OK、build exit 0。
  再生成ファイルはブランチの `search-infra/examples/L_meta_2229.lean` に置いた）
  → **A 型ステップは宣言文を渡すだけで、ガード込みで提出ファイルまで作れる**

### M4 調査: B は3亜種（`search-infra/m4-survey.md`）
- **B-promise**（RepSizeAtMost / マスク型）: ライブラリほぼ完備。Promise.lean は Link2 の `enc2`
  （= Defs の enc + fLex、単調・NOT 無し）を使う。接続点は `rep_lower_mask (n m M s)`
  （PromiseGen.lean の79行目）で、必要なのは
  `¬ FormulaSat (enc2 (n+m) s (gMask n m M) (repRows n m))`
- **B-readcount**（lineDegrees による読み取り回数上限）: ライブラリ支援なし。例 L_meta_1388 の証明構造の読解から
- **B-firstgate**: 名前で引ける実例は未発見。デスクの実例待ち

### M4 promise: CNF 生成器の検証通過
- `search-infra/genpromise.py`: `enc2 (n+m) s (gMask n m M) (repRows n m)` の CNF を生成。
  Lean 本体の #eval 出力と **341節すべて順序込みで完全一致**を検証済み（n=2, m=2, M=11, s=2）
- 配線部品も作成済み: `search-infra/genpromiserow.py`（promise 用の行ファイル生成器。検査対象の
  公式は Lean の enc2 自体で、CNF は証明書ヒントの読み取り専用）、`search-infra/mkpromiserow.py`
  （(n, m, M, s) → genpromise → CaDiCaL → genpromiserow のワンコマンド）

## 公式チェッカーの裏付け（2026-11-27）

- Claude Code が `examples/L_meta_2229.lean`（取り込み器 v2 の再生成版）を公式チェッカーに通し
  **ACCEPTED**（138秒、公理は標準3つのみ）。宣言文はマージ済み版と完全一致、ガード3段階通過、
  import は `PEqualNP.Defs` のみ。A 型は「宣言文を渡すだけで提出できるファイルが出る」ことが
  公式に裏付けられた。ローカルで完走しないのは VM 性能の問題。提出前の最終確認は、生成ファイルを
  ブランチに置けば Claude Code 側で代行可能。

## 完了した追加分（2026-11-27）

- B-promise 通し: mkpromiserow 生成ファイルが `rep_lower_mask` 経由で lake build 成功
  （生成器の3件の不具合を修正: FormulaSat の完全修飾、`Nat.testBit` 形式、RepSizeAtMost の修飾）
- 分類器に promise-mask 抽出（(n, m, M, s) を抜いて mkpromiserow-ready と判定）を追加
- M5（方向4）: 2×2 マスク M=11 の exact-size を通しで確認。回路合成器 `gensynth.py` を追加し、
  既知ケース 4×4 マスク359 で6ゲート（正解サイズ一致）を合成、up 定理のビルドも通過
- B-readcount: L_meta_1388 は LRAT を使わない手書き組合せ論法と判明。パイプライン化対象外

## 未完了・次の手

1. link 特化型（L_meta_3644 型、SAT 不要）の自動化 — 実施中
2. 規模の壁: `enc2` の対称性除去で証明書がどれだけ縮むか実測。cube 分割を帰着ファイルで
   別ステップにする案の検討
3. promise / exact 系の提出形（取り込み器で PromiseGen 系も内包する拡張）。実ステップを
   受けた時に合わせて作るのが無駄がない
4. B-firstgate: desk に実例が出るまで保留

## 作業記録

- 計画と進捗ログ: `search-infra/PLAN.md`、調査メモ: `search-infra/m4-survey.md`、
  取り込み器の設計メモ: `search-infra/importer-design.md`
