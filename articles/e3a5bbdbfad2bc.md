---
title: "Leanに入門したい"
emoji: "👻"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: []
published: false
---

導入

型と項

自然数の型Nat
ライブラリで定義されている
自動的に読み込まれる。

# 項と型

項は型を持ちます。
#checkで項の型を調べることができる。

```
#check 1
```
1はNat型を持ちます。

型自体も項です
```
#check Nat
```
NatはType型を持ちます。

Typeも項であり、型を持ちます。
```
#check Type
```
