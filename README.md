# 高階パターン単一化のUnboundライブラリを用いたHaskellによる実装

Weirich の Unbound ライブラリを用いた高階パターン単一化の実装

# File
* src/alphabetic.hs
Nipkow が ML で実装したコードを Haskell に書き直したコード。

* src/alphabeticUnbound.hs
上記のコードを Unbound を使って実装したコード。

# Requirement
* Stack
* (Cabal でも動くかもしれないですが、未検証です)

# Intallation
```bash
cd ho-unif-Unbound
stack install
cd src
stack ghci alphabetic.hs
stack ghci alphabeticUnbound.hs
```
# Usage
alphabetic.hs、alphabeticUnbound.hs ともに unifP が単一化をする関数となる。
入力は文字列で行い、データ型への変換はパーサーが行う。

例えば、alphabetic.hs で λx,y.F(x) と λx,y.c(G(y, x)) の単一化をする場合、
(F,G は自由変数、cは定数)
```ghci
unifP "Lx,y.F(#x)" "Lx,y._c(G(#y, #x))"
```
束縛変数には #、定数には _ をつける必要がある。

一方、alphabeticUnbound.hs で λx,y.F(x) と λx,y.c(G(y, x)) の単一化をする場合、
```ghci
unifP "Lx,y.F(x)" "Lx,y._c(G(y, x))"
```
となり、変数の区別は必要ない。
