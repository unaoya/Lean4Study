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
項と型は排他的な概念ではない、普通の数学で要素と集合がそうであるのと同じように。

項:型、という書き方が基本です。:がだいじ。
:の左が項、右が型。

項が基本的な対象で、（おそらく）すべての項に型がついています。
#checkで項の型を調べることができます。

```
#check 0
#check 1
#check 2
```
0, 1, 2はそれぞれ項であり、いずれもNat型を持ちます。

Natも項です。
```
#check Nat
```
NatはType型を持ちます。

Typeも項です。
```
#check Type
```
TypeはType 1型を持ちます。

項を定義します。
defを使います。

```
def x : Nat := 1
#check x
```

Nat型を持つ項xを定義し、その値？として1を割り当てる？1も項なので、項に項を割り当てるというべきか？

```
def y := 1
#check x
```

defと:=は項では（おそらく）ありません。

変数の定義とは違うことに注意。

Type型の項を定義することもできます。

関数を定義しましょう。

# 命題も型である

# 証明を書く

# Natの中身
