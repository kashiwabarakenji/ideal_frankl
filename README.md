# 根付きサーキットと、閉包作用素と、閉集合族。フランクルの予想にからめて。

## 概要

共通部分で閉じた集合族に関する予想であるフランクルの予想を考えたい。
集合族が共通部分で閉じた上に、全体集合を持つことを仮定しても、予想として、同値になる。
共通部分で閉じていて、全体集合を持つような集合族は、閉集合族(Closure System)と呼ばれていて、根付きサーキット(Rooted Circuits)で表現できることが知られている。フランクルの予想は、閉集合族は、rareな頂点を持つというものである。rareな頂点とは、集合族の要素を半分以下しか含まない頂点のことである。フランクルの予想は解決していないが、考える集合族を根付きサーキットの条件から絞ることによって、部分的な解決を目指す。

現在証明したことのうち、主要な結果が3つある。
- ステムサイズがすべて1の根付き集合から生成される集合族の完全根付きサーキット表現は、すべてステムサイズが1である。
- ステムサイズがすべて1の根付きサーキットには、rareな頂点が存在する。
- 根付きサーキットの根を持たない頂点があれば、rareな頂点になる。

これらは、すべて、根付き集合のイメージを持っている人や、自然言語による証明では自明といってもいい言明であるが、形式的に証明すると、補題がいくつか必要だったりして、簡単ではない。

## 定義と各ファイルの説明

数学的な定義や言明に関しては、Lean 4で記述している。Lean 4のコードは、このGitHubリポジトリのrootedのフォルダの下の各ファイルにある。(別のフォルダは別の古いプロジェクトが入っていて、このREADMEの対象外である。)
Leanのファイルは、相互にimportしないように作成するので、以下のファイルに関して、記述の上のほうのファイルがimportされる側の基本的なファイルになっている。

### 基本的定義 (CommonDefinition.lean)

有限台集合上の集合族(SetFamily)を考える。集合族の要素をhyperedgeと呼んでいる。
閉集合族(Closure System)とは、共通部分で閉じていて、全体集合をhyperedgeとして持つ集合族である。
次数(degree)やhyperedgeの数(number_of_hyperedges)についても定義している。

### 閉集合族と閉包作用素 (ClosureOperator.lean)

閉包作用素(Closure Operator)については、ClosureOperator.leanで、定義や定理を扱っている。
閉集合族が、閉包作用素から定義される閉集合の全体と一致するための必要十分条件として、
extensive, monotone, idempotentの3つの条件が知られているが、その同値性について証明をおこなっている。
その際に、閉集合族が与えられた時に、集合の閉包が、その集合を含むhyperedge全体の共通部分として定義されている。

### 2項関係から導かれる前順序 (Preorder.lean)

Preorder.leanは、有限集合上の2項関係の推移的閉包で表現されるようなpreorderに関する定義や定理である。
hyperedgeとして、この前順序で下に閉じているような集合、いわゆるorder idealを考えて、order idealに関する閉包作用素についての言明を証明している。たとえば、与えられた頂点集合に関して、そのある要素の下にある要素を集めた全体と、その頂点集合を含むようなideal全体の共通部分は一致することなどを示している。ここでのidealの意味は、イデアル集合族を考えていたときのidealとは無関係である。イデアル集合族は、包含関係に関する順序を考えていたが、ここでのidealは、頂点間の順序である。

集合SがR x yという2項関係に関して、yは含んでxを含まないことを両立(compatible)しないと呼んでいる。
2項関係が与えられた時に、推移的閉包をとっても、両立する集合全体は変わらないことも証明している。

このファイル内では、台集合を仮定せずに、考えている世界全部であるType alphaを全体集合として議論している。他のファイル内では、alphaの中に全体集合を考えている。それは、マイナー操作などで、台集合が変わったりすることがあるからである。台集合を考える場合は、Lean 4のsubtypeを用いて議論している。Preorderにおける2項関係は、ステムサイズ1の根付きサーキットの関係を抽象化している。Preorder.leanでは、subtypeも出てこないし、ステムサイズが2以上に相当するものが登場しないので、ひたすら頂点間の2項関係だけから議論しており、定理の証明などがすっきりしている。証明されていることは、2項関係の世界では知られている内容だと思われるが、Lean 4で定式化されているかは不明。

StemSizeOneのファイルにおいて、Preorderだけで考えた世界は、ステムサイズが1の根付きサーキットしか持たないものと同値であることが示されている。

### 根付き集合族 (RootedSets.lean)

根付き集合族に関しては、RootedSets.leanで記述している。根付き集合とは、通常は、集合内の1点とペアにした集合のことだが、ここでは、1点と1点以外の集合上の点に分けて、1点以外をステム(stem)と呼んで、根(root)と呼ぶ。そのペアは、Lean上ではValidPairと呼んで、rootがstemに含まれないという条件も合わせた三つ組になっている。

根付き集合の族RSから集合族を考えることができる。Sが根付き集合(stem,root)と両立しない、rootを含まずに、stemを部分集合として含む場合である。RSの任意の根付き集合と両立するような集合族を、RSが表現する集合族と呼ぶことにする。閉集合族になる。逆に閉集合族から両立するような根付き集合を集めてきて、根付き集合の族を作ることができる。RSから閉集合族を作って、根付き集合族を作るとRSを含むような根付き集合族ができて、対応する閉集合族は一致する。閉集合族から作れる根付きサーキットの族を完全表現(complete representation)と呼ぶことにする。

### 根付きサーキット (RootedCircuits.lean)

根付き集合の完全表現のなかで、rootが同じものの全体を考えた時に、ステムの包含関係で極小なものだけを考えても、表現する閉集合族は変わらない。このようなステムの包含関係で極小な根付き集合を根付きサーキットと呼ぶ。

### 根付き集合のimplication (RootedImplication.lean)

RootedSetsのimplicationの関係について扱っている。この根付き集合と、この根付き集合があれば、この根付き集合があるなど。また、現状では、ステムサイズが1の根付き集合によって、頂点間にPreorderが生成されることについての証明も入っている。現状では、2項関係の記号など、StemSizeOne.lean との記述が統一されていない部分もある。
singleton hyperedgeと、ステムサイズ1の根つき集合の関係の証明もここで行なっている。

### 閉集合族のマイナーであるtrace (ClosureMinors.lean)

閉集合族のマイナー操作に関しては、とりあえずtraceを考えている。ClosureMinors.leanで記述している。パラレルな頂点を除去するときなどに使われる。閉集合族のtraceは、再び閉集合族になることも証明している。

### Parallelな頂点 (Parallel.lean)

パラレルな頂点に関しては、Parallel.leanで記述している。頂点ペアがパラレルとは、任意のhyperedgeに関して、同時に含まれるか、含まれないかが一致する2頂点である。

パラレルな頂点ペアが存在するときに、その一方をtraceしても、次数は変わらずに、rare頂点が存在するかどうかも変わらないことを示した。よって、Franklの予想の解決には、Parallelな頂点がないものを考えれば十分であることも形式的に示した。

### RootedFrankl.lean

rareな頂点の存在定理など、フランクルの予想に関係がある内容が記述されている。根付き集合の根が存在しない頂点は、rareであることを証明した。頂点を含まないhyperedge全体から頂点を含むhyperedge全体への単射の存在から、rareであることを示すなどの補題を利用して証明されている。

### StemSizeOne.lean

ステムサイズがすべて1の根付き集合から生成される集合族の完全根付きサーキット表現は、すべてステムサイズが1であることが、主定理。その証明のために必要な補題もいくつか示す。
ステムサイズがすべて1の根付きサーキットには、rareな頂点が存在することの証明も行なっている。順序集合のidealの全体は、distributive latticeになるので、既知の結果であるdistributive latticeにrare vertexが存在するということに対応している。

### Bridge.lean

Hyperedgeがすべて通る点をbridgeと呼ぶ。ブリッジをtraceしても、hyperedge数や、その他の点の次数やrareかどうかは変化がないことを示している。他のファイルとはわりと独立した内容。閉集合族が空集合を持つことと、ステムサイズが0の根付きサーキットを持つことが同値であることも証明している。閉集合族が空集合を持つとしても、フランクルの予想の強弱には影響しないことも証明している。

### Hyperedge.lean

台集合の大きさから-1や-2の大きさのhyperedgeを持つとフランクルの予想の反例になり得ないという基本的な定理を証明した。そのために、2点優位と2点平均abundantが同値であることの証明も行った。2点平均abundantとは、2点{x,y}に対して、すべてのhyperedge数からxとyの次数を引いたものが負であること。2点優位とは、{x,y}を含むhyperedgeのほうが、2点とdisjointなhyperedgeよりも多いこと。

## 安部の定理の形式化

T. Abe Strongly semimodular lattice and Frankl's conjectureでは、束上でのrare vertexの存在の十分条件を与えた。それと同値な定理を閉集合族の世界に翻訳して、Lean 4で証明した。
十分条件として満たすべき条件が2つある。
1つ目は、Dash条件と呼んでいる、サイズ1の根つき集合の根となりうる点の全体のclosureをXのに属さない点が存在するという条件。
Dash作用素を、hyperedge Xを、Xに含まれるサイズ1の根つき集合の根となりうる点全体のclosureに移す作用素とする。Dash条件は、全体集合はDash作用素によって全体集合に移らないと言い換えることができる。
2つ目は、Plus条件と呼んでいて、任意のhyperedge Xに対して、Xに包含関係でカバーされるような極大な集合の共通部分となるhyperedgeが、Dash Xの部分集合になるという条件である。この条件を満たす時にDash条件により、全体集合のDashによる移り先にならなかった点がrareになるというのが、Abeの定理である。

Abe.leanのファイルの以下の定理がLean 4で形式化した言明になる。

```lean
theorem abetype_theorem (SF:ClosureSystem α)  [DecidablePred SF.sets]:
   plus_condition SF → ∀ v : α, v ∈ SF.ground \ ((dash SF SF.ground.attach).image Subtype.val) → SF.is_rare v
```
## 安部の定理の一般形

「すべての根つきサーキットのサイズが1の集合族は、rare vertexを持つ」という言明を前に証明したが、この閉集合族は、Dash作用素とPlus作用素が常に一致するので、Plus条件を満たす。パラレルな頂点が存在しないと仮定すると、Dash条件も満たす。安部の定理は、一般的な言明を特殊な状況であるstrongly submodular lattice(Plus作用素とDash作用素が一致する)に当てはめるための言明なので、かなり状況が制限されている。

abeの定理のタイプの一般的な形を考える。安部の論文ではDashの作用素がステムサイズが1の根だけを考えていたが、ステムサイズがk以下の根に拡張してもDash作用素の包含関係に関する単調性が成り立つので、根の集合のclosureに属さない点があれば、rareになることが証明できる。作用素が包含関係で単調で、全体集合の作用素の像が全体集合にならなければよい。もっとも一般的には、どのhyperedge XのX+に含まれない頂点があれば、rareになる。この言明をLean 4で証明した(abetyoe_theorem_general)。

```lean
theorem abetype_theorem_general (SF:ClosureSystem α)  [DecidablePred SF.sets](v: SF.ground):
   (∀ X:Finset SF.ground, v ∉ (coveringIntersection_sub SF X)) → SF.is_rare v 
```

頂点を含むhyperedgeの全体から、含まないhyperedgeへの単射の構成により、rareであることを示すタイプの定理は大抵この形になっている。以下は全部、この形である。
- lower semi-modular lattice。
- 頂点上の半順序 (distributive latticeなので、lower semi-modularの特殊ケースともいえる。)
- 根が存在しない頂点。
- イデアル集合族

これは、任意のhyperedge Xに制限しても、xを含む部分が「最初にとれる」という条件である。

## これからの拡張予定

この分野の将来的な目標としては、ステムサイズが2以下で生成されるような閉集合族に関して、rareな頂点が存在することを示したい。
Leanによらない証明もわかっていない。
