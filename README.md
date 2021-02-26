# 高階パターン単一化のUnboundライブラリを用いたHaskellによる実装

Weirich の Unbound ライブラリを用いた高階パターン単一化の実装

# File
* src/alphabetic.hs
Nipkow が ML で実装したコードを Haskell に書き直したコード。

* src/alphabeticUnbound.hs
上記のコードを Unbound を使って実装したコード。

# Requirement
* Stack

# Intallation
```bash
stack install
cd src
stack ghci alphabetic.hs
stack ghci alphabeticUnbound.hs
```
