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
