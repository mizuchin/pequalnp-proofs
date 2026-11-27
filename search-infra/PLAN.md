# pequalnp 探索基盤（LRAT パイプライン）作業記録

指示書: `~/workspace/user/files/search-infra-spec.md`（Claude Code 作成、2026-11-26 ユーザーから受領）
一次資料: https://pequalnp.com/join.txt（2026-11-26 03:29 JST 時点で最新を確認済み。beat は5分ごと）

## 棲み分け（Claude Code との衝突回避）

- こちらの作業場所は `~/workspace/pequalnp-muse/` 配下だけを使う。Claude Code 側のクローンには触らない。
- こちらのクローン: `~/workspace/pequalnp-muse/pequalnp-proofs`（上流 open-goat の clone、remote=origin のみ、main は clean に保つ）
- 作業はブランチ `muse/search-infra` 系で行い、main 直下の既存ファイルは変更しない（指示書 §6）。
- 提出段階になったらユーザーのフォークを使う。VM の gh ログインは 2026-11-26 03:33 に完了（mizuchin、device code 方式）。クローンの remote は origin=mizuchin/pequalnp-proofs、upstream=open-goat/pequalnp-proofs に付け替え済み（pnp.sh submit が origin へ push するため）。コミット作者は noreply アドレスに設定済み。pnp.sh を使うときは PATH に ~/.elan/bin が要る。

## 作業の型（2026-11-26、ユーザー経由で Claude Code の運用に合わせて採用）

- 作業のたびに、まず上流の最新を取り込んでからビルドする: `git fetch upstream` → `git merge --ff-only upstream/main`（こちらの main には独自コミットを積まないので常に fast-forward できる）→ 必要なモジュールを `lake build`
- 理由: 上流は2日で6000コミット超のペースで動き、古いツリーで作った証明は Library / Defs の変更で壊れたり、宣言文の前提が変わったりしうる。チェッカーもツリーのビルド設定がコミットと一致することを要求する

## 環境（2026-11-26 確認）

- prep 完了済み（01:32）: elan、Lean 4.36.0 toolchain、Mathlib キャッシュ取得 rc=0
- クローンは最新 main（e125f04d）に追随、指示書 §2 の資産は全て存在を確認:
  Library/LRAT/{Checker,Link,Link2,LinkN,LinkN2,Cube,Promise,PromiseCube,PromiseGen}.lean、
  Defs/LratEncoding.lean、notes/data/lrat-link/{genmono,gennot,genrow,mkrow,decode}.py、
  Outside の見本 L_meta_10000.lean（468K）/ L_meta_3644.lean / L_meta_2523.lean（260K）
- 未導入: CaDiCaL（mkrow.py が `cadical` コマンドを呼ぶ）→ ソースからビルドして `~/workspace/pequalnp-muse/bin/` に置く
- VM: 4コア、メモリ available が小さい時間帯がある。重い lake build は余裕のあるときに回す（ユーザーの指示どおり）

## マイルストーン（指示書 §5）

1. [ ] 再現: 採用済み LRAT 系ファイルを1つ選び、mkrow.py から同じ主張を作り直し、手元の公式チェッカー（tools/check-lean.mjs）で ACCEPTED にする。取り込み器のテストを兼ねる
2. [ ] 小規模性能表: n=4〜9、s を変えて CNF サイズ / ソルバー時間 / LRAT サイズ / Lean ファイルサイズ / チェック時間を表にする
3. [ ] 分類器（.pnp/<id>.json の gap.statement から A/B/C 判定）と A の完全自動化（取り込み器を含む）
4. [ ] B のつなぎ補題: 最初のゲート固定、読み取り回数上限、派生入力の3種
5. [ ] 方向4（NOT 1つ）の正の側を1件、端から端まで通す

各段階の「完了」は、生成した Lean ファイルが手元の公式チェッカーを通ること。

### マイルストーン1の進め方（2026-11-26 に精査）

- genrow.py の出力は、名前空間内に rows / F / 証明書（fk・words 相当）/ unsat / lower（`lower_of_unsat` 経由）を置く形。マージ済みの L_meta_2229 は checkW（Checker の分割検査）を使う別系統の生成で、バイト単位の再現にはならない。狙うのは「同じ主張（n=5, s=4, 同じ辺集合で 5 ≤ C.size）を作り直して通す」こと
- L_meta_2229 の宣言文には `ReadsBack 5 C` の仮定が余分にある（弱い主張）。genrow の lower はその仮定なしで証明するので、最終定理は仮定を捨てるだけで宣言文に一致させられる
- 公式チェッカーは `node tools/check-lean.mjs <lean file> <statement file>` の形で、statement file が要る。宣言文は L_meta_2229 の定理文から作る
- 前提として lean/ 側のプロジェクトライブラリ（Library.LRAT 等）のビルドが要る。Mathlib キャッシュは取得済みだがプロジェクト本体は未ビルドなので、初回はそこが一番重い。余裕のあるときに detached で回す

## 進捗ログ

- 2026-11-26 03:30 指示書を受領し着手。環境確認と一次資料の読み合わせ完了。CaDiCaL ビルドを detached で開始
- 2026-11-26 08:12 再実行ランが VM の置き換え（07:30 頃、uptime から確認）で中断していた。m1-repro.sh がチェッカー段階（verifier reading t=33s）で死に、ツリーの L_meta_2229.lean が再現版のまま残り、lean/.lake/check.lock も残っていた。死んだプロセスのロックなので手で除去し、ファイルを git checkout で復旧してから m1-repro.sh を再起動した（A/B は .done マーカーでスキップされ、段階 C から再開）。教訓: チェッカーの検証器は30分超の連続実行が要るのに VM 置き換えがそれを殺す。長時間のローカル検証は置き換えに弱い
- 2026-11-26 03:38 ユーザーがフォーク（2日前のフォークで 6238 commits behind だった）を GitHub 上で sync した。こちらのクローンも上流が e125f04d → c629ef36 まで進んでいた（fetch で確認）。上流の動きが速いので、実作業の前には必ず upstream を fetch して main を fast-forward すること。実行中のマイルストーン1ランは旧ツリーのまま完走させ、完了後に追随する
- 2026-11-26 03:32 マイルストーン1の再現対象を特定: `L_meta_2229.lean`（36KB、`lower_of_unsat` を使う採用済みファイルは他に L_meta_5531 のみ）。中身は n=5、s=4、辺 (0,3)(0,4)(1,2)(1,3)(1,4) の単調下界「5 ≤ C.size」で、rows=[3,5,6,9,10,17,18,28] は genmono の rows モード（最小の真・極大の偽）と一致する見込み。mkrow.py の引数は `5 4 03,04,12,13,14`。CaDiCaL 完成後に再生成して公式チェッカーで検証する。なおこのファイルは Library.LRAT を直接 import している（その gap の imports に含まれていたため）

## 進捗ログ（追記）
- 2026-11-26 10:46 ユーザー決定: マイルストーン1の手元完了条件を「再生成の一致＋生成ファイルの lake build 通過」に置き直し、公式チェッカー判定は提出時にプロジェクト側へ委ねる。M1 完了。
- 2026-11-26 10:47 マイルストーン2開始: `search-infra/m2-run.sh`（upstream へ ff → LRAT 再ビルド → `m2-perf.py`）。対象は cycle グラフ C_n（n=4〜9、s=3,4,5、n≥7 は s=6 も）と M1 アンカー K23。設定ごとに CSV へ追記するので VM 置き換えでも最大1設定分しか失わない。ログ `search-infra/m2.log`、結果 `search-infra/perf/perf.csv`。
- 2026-11-26 11:11 マイルストーン2完了（ALL DONE、22設定）。C4 は全て SAT（cycle は factorize するので UNSAT family として貧弱）。CaDiCaL は全設定 0.54s 以下。Lean ビルドは s=5 まで 12〜54s（C5_5_3 の 200.0s は初回ビルドのキャッシュ温めと思われる）、s=6 は約225s。512 KiB 制限は s=6 から噛む（C7_7_6 1,916,221 B、C8_8_6 1,982,798 B、C9_9_6 2,153,763 B）。唯一の失敗は C9_9_6 のビルド：Lean が exit 137（OOM kill）で死亡、再現ビルドでも同じく 137 を確認（ログ `~/workspace/goals/pequalnp-lrat/hidden_files/m2-c9_9_6-build-repro.log`）。証明書の誤りではなく VM のメモリ不足。結果を P vs NP サイドチャットへ報告済み。
- 2026-11-26 16:25 マイルストーン3開始: 分類器 `search-infra/classify.py` 初版。検証: L_meta_2229→A（ReadsBack は落とせる付帯条件として注記）、L_meta_3644→C（FormulaSat の SAT 側）、L_meta_5531→B（RepSizeAtMost の上限∧下限の正確サイズ型。下半分はパイプライン可、上半分は明示回路が要る）、L_meta_10000/10002→C（被覆問題系）。抽出は最終定理の宣言文を最初の `:=` までで取る形に緩めた。
- 2026-11-26 16:29 取り込み器 v1 のビルドテスト通過: `search-infra/importer.py` で Checker.lean + Link.lean を `PEqualNP.Outside.L_meta_2229_aux` の下に取り込んだ 146,002 bytes の自己完結ファイルを生成し、lake build が exit 0（2m23s）で通過。Checker.lean は import が無く、Link.lean の project import（Defs.MetaComplexityLgpMono、MetaComplexity.Helpers.Shannon）は先頭へ hoist。残りはパイプライン全体の配線（分類→生成→取り込み→整形→ビルド）と、分類器の B/C 側の拡充。
- 2026-11-26 16:46 パイプライン統合テスト PIPELINE OK: L_meta_2229 の宣言文だけを入力に、分類A → n=5 s=4 辺03,04,12,13,14 を読み取り → mkrow → 取り込み器 → 整形（148,304 bytes、512 KiB 内）→ lake build exit 0。A 型ステップは「宣言文を渡すだけ」で提出ファイルまで作れる。ツリーはテスト後に復旧済み。
- 2026-11-26 16:46 マイルストーン3完了: `pipeline.py` 統合テスト通過（宣言文のみ入力→分類A→生成→取り込み→整形 148,304B→lake build exit 0）。次は M4（B つなぎ補題）・M5（方向4）。
- 2026-11-26 21:31 マイルストーン4調査完了（`search-infra/m4-survey.md`）: B は3亜種に分かれる。B-promise（RepSizeAtMost / マスク型）はライブラリがほぼ揃っており、残りは `enc2` の CNF 生成器 `genpromise.py` のみ。B-readcount はライブラリ無し（L_meta_1388 の証明構造の読解から）。B-firstgate は実例未発見。攻撃順序は promise → readcount → firstgate。
- 2026-11-27 01:20 `genpromise.py` 検証通過: Promise.lean は Link2 の enc2（単調 enc + fLex、NOT ゲート無し）を使うことを確認。`genpromise.py`（n=2,m=2,M=11,s=2）の出力 CNF は、Lean 本体の `enc2 4 2 (gMask 2 2 11) (repRows 2 2)` の #eval 出力を DIMACS へ変換したものと、341節すべて順序込みで完全一致。検証用スクラッチファイルは除去しツリーは clean。残りは CaDiCaL → `genrow.py --enc2` → `rep_lower_mask` による最終定理までの配線。
- 2026-11-27 09:04 Claude Code のレビュー対応: 書式ガード（outside-guard.mjs はコメント含む生テキスト走査）で取り込みファイルが拒否される問題を修正。importer v2: ライブラリ部分のコメント全除去、`macro "wdt"` を削除し使用13件を展開形に置換、import は `PEqualNP.Defs` のみ、Shannon の wire-fold 補題6件（wiresFrom_prefix 含む）を aux 名前空間へコピー、open から Helpers を除去。pipeline にガード3コマンド（gap-of-file/imports/closure）を整形後・ビルド前へ追加。L_meta_2229 再生成で GUARD OK + lake build exit 0（137,262 bytes）。指摘の訂正: `rep_lower_mask` は PromiseGen.lean 79行目。新分類候補: 「link 特化型」（L_meta_3644 = Link.lean の `link` を n=10, s=14 に特化）。

### 2026-11-27 09:1x JST — B-promise 通し完了・分類器拡張・readcount 読解

- B-promise end-to-end 動作確認: mkpromiserow (2 2 11 0) の生成ファイルが lake build exit 0。
  genpromiserow.py に3件の修正: (1) unsat の FormulaSat を PEqualNP.Defs.LratEncoding.FormulaSat に
  完全修飾（Checker 側と同名で ambiguous だった）、seg0 の ClauseSat も Checker 側に修飾。
  (2) lower の `{M}.testBit` は数値リテラルとして構文エラーになるため `Nat.testBit {M}` に。
  (3) RepSizeAtMost は開いた名前空間に無いため PEqualNP.Represents.RepSizeAtMost に修飾。
  生成器はこれまでビルド未検証だったことが判明（今回が初の通し）。
- classify.py に promise-mask 抽出を追加: ¬ RepSizeAtMost (fun (u : Fin n) (v : Fin m) =>
  M.testBit (m * u + v)) s の形から (n, m, M, s) を抜いて B / mkpromiserow-ready と判定。
  testBit でない RepSizeAtMost 下界は B / promise-other。検証: 規範形2件・L_meta_5531（exact のまま）・
  L_meta_10055（promise-other）・L_meta_2229（A のまま）。
- B-readcount: L_meta_1388 は LRAT を使わない手書き組合せ論法（m4-survey.md に記録）。
  パイプライン化の対象外と判断し保留。

### 2026-11-27 09:2x JST — マイルストーン5（方向4）完了

- 小ケース通し: 2×2 マスク M=11 の exact-size（=1）を、下半分 mkpromiserow+rep_lower_mask、
  上半分 明示回路1ゲート、下半分と desk 形式（(11 : ℕ).testBit / u.val）の conjunction まで
  1ファイルで lake build exit 0。
- 回路合成器 gensynth.py を追加: unit 行上のマスクに対する DAG 共有つきレベル探索。
  M=11 → 1ゲート [or(0,3)]、既知の正解ケース 4×4 M=359 → 6ゲート（0.08秒、L_meta_5531 の
  サイズと一致）。合成回路での up 定理（RepSizeAtMost 359 6）も単体でビルド通過。
- これで仕様のマイルストーン 1〜5 は一通り完了。残件: B-firstgate（desk の実例待ち）、
  exact-size の pipeline 統合（分類器は exact を検出済み。mkexact 相当の整形は未実装）、
  提出可能形への importer 適用（promise/exact 系は library import 前提の生成で、
  取り込み器の対象は現状 A 型のみ）。

### 2026-11-27 09:2x JST — 分類器のマスク抽出、desk 形式への対応漏れを修正

- 振り返りで判明: promise-mask 抽出はライブラリ形式 (`M.testBit (m * u + v)`、binder 別々)
  しか拾えず、実際の desk 形式 (`(359 : ℕ).testBit (4 * u.val + v.val)`、共有 binder
  `fun u v : Fin 4`) は promise-other に落ちていた。抽出正規表現を拡張し、ascription 形・
  Nat.testBit 形・u.val 形・共有 binder に対応。5531-low の desk 形が n=4 m=4 M=359 s=5
  で抽出されることを確認。既存の検証ケース（5531 exact、10055、2229）に退行なし。

### 2026-11-27 09:24 JST — 公式チェッカー ACCEPTED（Claude Code 側で実施）

- Claude Code が examples/L_meta_2229.lean（取り込み器 v2 の再生成版）を公式チェッカーに通し
  **ACCEPTED**（138秒、公理は標準3つのみ、カーネル再検査 2373 定数）。宣言文はマージ済み版と
  完全一致、ガード3段階通過、import は PEqualNP.Defs のみ（上流版より厳しい条件）。
  これで A 型は「宣言文を渡すだけで提出できるファイルが出る」ことが公式に裏付けられた。
  ローカルで完走しないのは VM 性能の問題と確定。提出前の最終確認は生成ファイルを
  ブランチに置けば Claude Code 側で代行可能（先方からの申し出）。
- 次の重点（先方の指摘）: (1) 規模の壁 — enc2 の対称性除去で証明書を縮める / cube 分割を
  帰着ファイルで別ステップにする。(2) link 特化型（L_meta_3644 型、SAT 不要）の自動化。

### 2026-11-27 09:3x JST — link 特化型の自動化 + enc2 縮小率の実測

- 分類器に新カテゴリ L（link 特化型）を追加: Monotone2 仮定のもと結論が FormulaSat (enc N S …)
  の ∀ 形を検出し (n, s) を抽出。L_meta_3644 で検証（2229=A、5531=B-exact に回帰なし）。
- pipeline.py に L 分岐を追加: 生成部なし（空の raw）で取り込み器を通し、最終定理は
  valid_ofCirc → exists_nf → enc_sat/val の固定テンプレート。L_meta_3644 の宣言文で通し実行し
  **PIPELINE OK**（67,354 バイト、ガード通過、lake build 成功）。SAT 不要で機械生成できる。
- enc2（対称性除去）の縮小率実測: genenc2.py（genpromise の符号化を全行・辺関数に適応）で
  s=6 の LRAT サイズを enc と比較。C7: 586,082 vs 1,959,348（3.3倍縮小）、C8: 718,129 vs
  1,985,436（2.8倍）、C9: 1,456,081 vs 2,088,969（1.4倍）。n が大きいほど効果は薄れる。
  生 LRAT では s=6 でも全て 512 KiB 超（パック後は C7 が境界付近）。Link2 に lower_of_unsat2 が
  あるので A 型の enc2 移行自体は可能だが、desk の s=13〜16 には届かず、cube 分割＋帰着が本道。

### 2026-11-27 09:30 JST — 受付の全件集計（Claude Code が実施）: 方針転換の提案

- 受付の全 4384 件（11/27 00:23 UTC 取得）を分類器で集計: 今すぐ受け取れる 23 件、
  取り組み中 467、配布対象外 3893。A 型は **0 件**、B は 47 件（全て対象外か取り組み中）、
  link 特化型 1 件（対象外）。つまり下界パイプラインが今すぐ使えるステップは 0 件。
- 受け取れる 23 件はほぼ全て「k ゲート以下の回路が存在する」を示す **回路発見型**（上界側）:
  3×3 完全マッチングを 11〜13 ゲート、4×5/4×6 約束問題を 9〜10 ゲート、two-lit を小回路、
  5×5 表を 7〜9 ゲート、大規模族（150〜1350 ゲート）など。
- 部品の在庫確認（Muse 側）: notes/data/lrat-link/decode.py が実在し、genmono の CNF が
  SAT のときモデルから回路を復元できる（下界用 CNF の裏側がそのまま発見用になる）。
  マスク型は gensynth.py が担当可能。一般の真理値表への一般化が残作業。
- 注意: 「Find it」とあるものは存在自体が未解決の可能性があり、見つからない場合もある。
- Claude Code からの提案: 次の目標を回路発見型に切り替えるのが最も成果に近い。
  小さいもの1件を先方で試すことも可能とのこと。ユーザーの判断待ち。

### 2026-11-27 09:3x JST — 回路発見型への着手（ユーザー判断「両方並行」）

- 分類器に U カテゴリを追加: find-mask（正の RepSizeAtMost + testBit、desk 形対応、
  gensynth-ready）、find-circuit（∃ Circuit + size ≤ k）、find-other。既存カテゴリに回帰なし。
- genfind.py: genmono の符号化を任意の真理値表に一般化（全行使用、padding で「≤ s ゲート」）。
  decode_find.py: モデル→回路の復元（padding/未到達ゲートの除去と再番号付け）、全行検証、
  Lean ゲート列の出力。復元器の再番号付けバグ（slot キーと wire 番号の衝突）を修正済み。
- テスト1 通過: C4 辺関数（n=4）を s=3 で SAT → 3ゲート回路を復元、全16行で検証一致。
- テスト2 実行中: 3×3 完全マッチング（9入力、真の行 247/512）を s=13→11 で合成試行中。

### 2026-11-27 10:08 JST — L-meta-23824 の分担（Claude Code と合意）

- ステップ: RepSizeAtMost (fun u: Fin 4 => fun v: Fin 6 => (1036159:ℕ).testBit (6u+v)) 10。
  data.pequalnp.com の snapshot part-022 から宣言文を自力取得（work/stmt23824.txt）。
- Claude Code 側: 全数探索で式型は全滅（9ゲート式なし、10ゲートで1変数2回もなし）、
  SAT 9ゲート UNSAT 確定。残るは部分式共有の DAG 型のみ。lease は Claude Code が保持。
- Muse 側: gensynth（DAG 探索）と genpromise CNF の CaDiCaL（LRAT 同時出力）を実行中。
- 合意: SAT なら復元したゲート列を Claude Code へ渡し、提出は lease 保持側から。
  UNSAT なら否定の双子ステップが受付に無い（00:23 時点で確認済み）ため提出不可。
  LRAT 証明書は statement_seems_false 返却の裏付け＋双子掲載時の提出材料として保管。
  先に結論を出した側が出たら、もう一方は止めてよい。
- 自分のテスト（3×3 マッチング mono+lex）は live ステップ優先のため停止した。

### 2026-11-27 10:11 JST — VM 置き換えで探索が2つとも死んだ（再起動済み）

- 10:11 JST ごろ VM 置き換え（uptime で確認）。gensynth（09:59〜）と CaDiCaL
  promise s=10（10:05〜）がともに消えた。CaDiCaL は 1.1GB・300万行の LRAT を
  部分的に吐いていたが、未完成のため破棄した。
- 10:15 JST に両方とも同じ設定で再起動した。gensynth timeout 1500s、CaDiCaL 2400s。

### 2026-11-27 10:18 JST — L-meta-23824 は受付が取り下げ、作業停止

- 取り下げ理由（受付）: 他の参加者が3回以上返却し、2時間提出なしのため規則 R-072 で打ち切り。
- 確定した部分結果: 9ゲート不可能（全数探索＋SAT UNSAT）。10ゲートの「1変数2回読みの式」も不可能。
  部分式共有の DAG 型は決着前に打ち切り。Muse 側の gensynth / CaDiCaL は結論なしで停止した。
- 教訓: 小さい発見型には他参加者が返却を重ねた「売れ残り」が混ざる。2時間無提出で取り下げが
  ありうるので、発見型は速く見切る／出たばかりを速く取るのがよい。Muse の SAT＋復元器は後者に合う。

### 2026-11-27 12:13 JST — L-meta-9809 終了／CEGAR の設計メモ

- L-meta-9809（14頂点19辺の辺関数、AND/OR/NOT ≤24）: 両側とも時間内に見つけられず。
  Claude 側は単調版（58行・約15万節）で既知の25ゲート回路すら30分で再発見できず、
  50分の区切りで `other` として返却予定。Muse 側の全行 NOT 符号化（4,105,750変数・
  33,953,460節・824MB）は CaDiCaL が2回とも OOM（前処理オフでも節の保持で上限）。
  Kissat ビルドは make ターゲット誤りで失敗したが、Claude の指示でこのステップへの
  資源投入は終了。CNF は work/find/p9809.cnf に保存（大きな機械向け）。
- 教訓（Claude の指摘）: 壁は行数よりゲート数そのもの。24〜25ゲート規模の合成は
  小さい式でも重い。24ゲートは「辺数＋被覆数−1」を破ることに当たり、存在しない可能性が高い。
- 設計メモ（次回の NOT 合成）: 全行符号化ではなく CEGAR で回す。最小行集合
  （辺行＋極大独立集合行）で解き、全入力で評価し、反例行だけ追加して解き直す。
  回路が実在すれば数十〜数百行で収束する見込み。genfind_not に行集合の外部指定と
  反例追加ループを足すのが実装形。

### 2026-11-27 13:40 JST — L-meta-25467 は判定つかず（事前調査）

- 5x5 crown-with-one-cell-removed, M=32435687, AND/OR ≤14。11:18 JST 時点で conjecture・試行0件。
- genpromise＋CaDiCaL を s=13, 14, 15, 16 で各20分かけたがすべて TIMEOUT（判定なし）。
  Table 1a の6件と違い、このマスクは VM の SAT では重い。VM での先行判定は不向き。
  次に来たら Kaggle（4コア・12h）か構造的な手作りが筋。L-meta-25468（NOT ≤9）は
  単調符号化の範囲外のため未着手。L-meta-25474 は同日中に checked 済みになった。

### 2026-11-28 01:20 JST — CEGAR for NOT-gate circuit finding 実装・検証完了

- 実装（2026-11-27 の設計メモ通り）:
  - `genfind_not.py` に `--rows FILE|LIST` を追加。行依存の節（source wiring・
    ゲート評価・出力）のみ指定行に制限し、構造節は不変。変数レイアウトも不変の
    ため `decode_find_not.py` はそのまま使える。既定は従来通り全行。
  - `decode_find_not.py` に `--bad-rows FILE` を追加。検証失敗時に不一致の
    全行を書き出す（CEGAR の反例収集用）。既定の動作は不変。
  - 新規 `cegar_find_not.py`（ドライバ）: 初期行集合は既定で辺行＋極大独立集合行。
    ループは CNF 生成→CaDiCaL→SAT なら復号して全行検証、失敗行を追加して
    再解。UNSAT は部分集合の緩和なので GLOBAL UNSAT として有効な判定。
    タイムアウト／反復上限は INCONCLUSIVE（判定なし）。終了コード 0=回路発見
    または GLOBAL UNSAT、2=判定なし。
- 検証結果（VM、CaDiCaL 2.2.1、--timeout 60）:
  - C4（n=4, 辺 01,12,23,03, s=3）: 1反復・6行で SUCCESS。既知の3ゲート回路
    or[1,3], or[0,2], and[4,5] を再発見し全16行で検証済み。
  - L_meta_2229 関数（n=5, 辺 03,04,12,13,14）: s=4 は GLOBAL UNSAT（8行で
    UNSAT）。全行符号化（32行・3846節）でも UNSAT を確認済みのため誤判定では
    ない。NOT を許しても4ゲートでは不可能で、真の最小は5。s=5 では3反復で
    SUCCESS（8行→10行→16行、5ゲート回路 and[1,2], or[0,1], or[3,5],
    or[4,7], and[6,8]、全32行で検証済み）。反復ごとに反例が 2行・6行と
    追加される、設計通りの CEGAR 動作。
  - C4 s=2: GLOBAL UNSAT（6行）。全行符号化でも UNSAT を確認済み。
- 訂正: 検証計画では L_meta_2229 関数を s=4 で回路発見と想定していたが、
  同関数は下界の事例（5ゲート必要）で、s=4 は正しく UNSAT。NOT を許しても
  最小は5のままで、NOT の節約はこの事例では起きない。
- 制限・注意: 変数数は行集合によらず 10*(s+1)*(2^n+n+s+1) のまま（レイアウト
  固定のため）。n=14 では宣言変数 4.1M のままになるが、節数は行数に比例して
  小さくなる。反例の追加は1反復あたり既定128行までで、多すぎる場合は均等間引き。
  L-meta-9809（n=14）には再投入していない。次回以降の NOT 合成ステップ用。
- 実行物: `work/find/cegar_4_3/`, `cegar_5_4/`, `cegar_5_5/`, `cegar_4_2/`
  （各 cegar.log に反復記録）。ブランチ muse/search-infra にコミット済み。
