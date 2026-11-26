# 取り込み器の設計メモ（マイルストーン3の下書き、2026-11-26）

## 目的
ステップの `imports` が `PEqualNP.Defs` のみ（+Mathlib）の場合、生成ファイルは
`PEqualNP.Library.LRAT.*` を import できない。必要なライブラリ部分をファイル自身の
名前空間へ取り込んだ自己完結ファイルに変換するのが取り込み器の仕事。

## 見本: L_meta_10000.lean（479,135 bytes、採用済み）
- import は Mathlib のみ（Mathlib.Logic.Equiv.Fintype、Mathlib.Tactic.Choose）。
- 全体を `namespace PEqualNP.Outside.L_meta_10000_aux` で包み、内側に `namespace LRAT`。
- Checker.lean の「adapted copy」がそのまま入り、末尾で aux 名前空間の定理を使って
  本体の宣言文を証明する形。
- コメントは残っている（m1 でコメントを全部消したのは自前の慎重さ。規則ではない）。

## 変換手順（案）
1. 元ファイル（mkrow/genrow 生成、Library import 版）を入力にする。
2. Checker.lean と、必要部分の Link.lean（lower_of_unsat とその依存）を取り込み元にする。
   - Defs への参照はそのまま（Defs は import 可）。
   - Library 内の相互参照は aux 名前空間内の相対参照へ書き換える。
   - `import PEqualNP.*` 行は除去し、Mathlib import は元ファイルと取り込み元の和集合。
3. 生成側の参照（例: `PEqualNP.Library.LRAT.Link.lower_of_unsat`）を aux 側の名前に差し替える。
4. 仕上げは m1 段階Bの後処理を一般化したもの: set_option の `in` 化、末尾に受付の
   宣言文どおりの最終定理を置き、内部の `lower` から導く。
5. 検証は新基準: lake build 通過（+ 書式ガード outside-guard.mjs があれば併用）。

## 未解決の論点
- genrow には Link 符号化と checkW 符号化がある（採用済み 2229 は checkW 側）。
  取り込み器がどちらの生成物を受けるかで、取り込むべきライブラリ部分が変わる。
  マイルストーン2の性能表でファイルサイズを見てから決める。
- Link.lean の依存の切り分け（lower_of_unsat が実際に使う宣言の集合）を
  `#print axioms` / 依存走査で機械的に取るか、手で固定リストにするか。

## 分類器（A/B/C）の入力
- `.pnp/<id>.json` の `gap.statement` と `imports` を読む。
- A: 単純な下界（辺関数、Monotone2/FanInTwo、付帯条件なし）→ mkrow 系で完全自動。
- B: 付帯条件つき（最初のゲート固定、読み取り回数、派生入力、約束）→ つなぎ補題が要る。
- C: それ以外（帰着 R_ ファイル等も含む）。
