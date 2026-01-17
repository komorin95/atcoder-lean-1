# atcoder-lean-1

LeanでAtCoderに参加するための作業用環境。
Rustでやっていたように提出ソースを溜め込むつもりは現状ない。
ライブラリを作ったり、テストスクリプトを書いたりする可能性はある。

## 使用法
`Main.lean`にLeanのソースを記述する。

## 実行
`lean exe atcoder-lean-1`を実行する。

## テスト
`lakefile.lean`の`io_examples`に入出力例を記述する。
`lake build`の後`lake test`を実行する。
