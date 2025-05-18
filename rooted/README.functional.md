# functional部分のREADME

## 言明

- Vを有限台集合として、関数 f:V -> Vが定義する前順序を考える。この前順序に順序ideal全体を考えて、有限集合V上の集合族と思う。
- この集合族が平均rareであることを示すのがメイン定理。

```haskel
theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0
```

## 前順序 (functionalCommon.lean)

- このファイルは、メイン定理を記述するために必要な定義と、それに関係する補題を記述している。
- Vを有限台集合とする。
- f:V -> Vの関数が与えられると、v < f(v)というV上の2項関係が定義できる。この2項関係のtransitive closureを考えるとV上に前順序(preorder)が定義できる。Setup.pre.le.
- vからみて、f(v)を親と呼ぶ。vとf(v)は異なると仮定しても同じ場合を許しても、予想としては同値になる。とりあえず異なると仮定して考えている。s.valid.
- 補題：functionが与えられると、前順序における頂点の同値類ができる。qClass_setup。- この同値類に対して、setoidを考えることができる。s.setoid.
- ここまでのsettingをSetupとして定義して、いろいろな言明の仮定として使っている。

## 前順序の性質 (functionalPreorder.lean)

- fから前順序を定義する時に、idealを考えてから前順序を考える方法と2項関係を考えて、そのtransitive closureを考える方法がある。どちらでも同じ前順序が得られる。size_one_preorder_setup_lemma
- 補題：前順序の大小関係と、親の関係で辿れるのは同値。iteratef_lemma, iteratef_lemma_ref
- 補題：同値類の大きさが2以上のところは極大要素である。eqClass_size_ge_two_implies_outside

## 同値類上の半順序の定義 (functionalTreePartialOrder.lean)
- 上のセッティングのもと、頂点の同値類上に半順序が定義できる。半順序関係の定義は、同値類Aから同値類Bに順序の大小があることを、任意の順序idealに対して、同値類Aを含んでいるならば同値類Bを含んでいるということと、定義する。partialOrder_from_preorder
- この枠組みをSetup2としている。仮定としての強さは、Setupと同じ。
- この2項関係は、半順序の公理を満たす。
- preorderとsetoid上のpartialOrderの関係を色々示す。pullback_preorder_lemma.pushforward_preorder_lemma
- 極大性is_MaximalQも定義して、preorderの極大性との関係を示す。isMaximal_iff
- fの同値類版が、fq。
- fとfqの関係も示す。f_on_equiv_n.
- fq単独の性質も示す。fq_lemma。

## 同値類上の半順序が作る集合族 (functionalSPO.lean)

- 前順序を前提にしないSetoidがSetup_spo。
- それに関する補題を証明している。
- Setup_spoとSetup2の関係

## 同値類上の半順序が作る集合族 (functionalTreeIdeal.lean)
- pre_closuresystemは、前順序から作ったideal。
- pre2_closuresystemは、Setup2のpoを利用して作ったideal。
- 補題：hyperedgeの集合の全体(=前順序の順序ideal全体)は、この半順序の順序idealに一致する。
- spo_closuresystemは、Setup_spoの仮定から作ったideal。
- 補題：spo_closreusystemは、pre2_closuresystemと一致する。

## 同値類上の半順序 (functionalSPO2.lean, functionalSPOtrace.lean)

- Setup_spoからsingleton_if_not_maximalの仮定をつけたのがSetup_spo2。
- Mainのファイルではこっちのほうを利用する。
- 補題：サイズが2以上の同値類は、半順序の極大要素に対応するところにしか出てこない。
- V上に同値類が与えられていて、以下の条件を満たすとする。1. サイズ2以上の同値類は、半順序の極大な要素のみ。2. 半順序の親は、たかだか1つ。
- この半順序に対して、順序idealを考えて、hyperedgeと思って、集合族を考えることができる。


## 順序idealと平均rare (functionalIdealRare.lean)

- 順序idealとは、考えている前順序で、下に閉じている集合のことである。
- 頂点集合上に前順序が与えられると順序idealの全体が決まる。これは集合族のhyperedgeと思って、平均rareになるかなどが議論できる。
- 平均rareとは、(順序idealの大きさの和*2-順序idealの個数*台集合の大きさ)<=0のことである。

## 同値類上の半順序とrare (functionalIdealRare.lean)

- 補題: サイズ2以上の同値類の頂点は、rareな頂点になる。
  - この補題の証明は、その同値類をhyperedge全体から含まないhyperedge全体への単射を作ることで可能。



## 半順序のtrace (functionalTraceIdeal.lean)


- 同値な頂点(パラレルな頂点とも呼ぶ)のひとつをtraceすることにより、同一視していく方向性。
- 補題: パラレルな頂点をtraceした場合、もとの前順序で大小関係があることと、traceした集合族での大小関係は一致する。ここでの大小関係は、hyperedgeがxを含んでいたらyも含むという関係。
  - よって、パラレルな頂点をtraceした集合族もこれにより、前順序を定めることができる。サイズ2以上の同値類から同値な頂点をひとつtraceしても、半順序の親がたかだか1つということも変わらない。
- 補題：サイズ2以上の同値類からパラレルな頂点をひとつtraceしても、サイズが2以上の同値類が極大なものに限られることも変わらない。
- 集合族としては、パラレルな頂点を持つ頂点をtraceしていくことにより、パラレルな頂点を持たない集合族を得ることができる。
- excessもここで定義。

## 半順序のtrace (functionalTraceIdeal2.lean)

- 補題： 集合族に対して、パラレルな要素を持つ要素で、rareな頂点をtraceして平均rareであれば、もともと平均rareである。
  - この補題は順序とは関係なく、一般に成り立つ。
- この補題の証明は、すでにParallel.leanのファイルの中で完了している。
- 補題: 集合族に対して、パラレルな要素を持つものが平均rareであることを示すためには、サイズ2以上の同値類をすべて1頂点にまでtraceしたものが平均rareであることを示せば良い。
  -パラレルな頂点の個数に関する帰納法で示すことができる。サイズがkの同値類があれば、k-1を足すということでbase caseが0にするとよい。

## 半順序と平均rare (functionalPartialOne.lean)

 - ここまでで、サイズ2以上の同値類はないと仮定してよくなったので、同値類のサイズは全部1で、頂点集合ground上の半順序と思うことができる。
 - パラレルな頂点がなくなったあとは、グラフ論の森(forest)で各連結成分に根が指定されているものと思うことができる。根から遠い頂点が下となる。
 - パラレルな頂点がなくなったあとは、極大な頂点(=グラフの根)をdeletionしていく。集合族としては、根のdeletionと考えても、traceと考えても同じ。
 - 補題：半順序集合の順序idealの個数は、台集合の数よりも同じか多い。
   - これは、各要素を単項idealに対応させれば、それが単射になることからわかる。反対称律から、単射でなければパラレルな要素が出てくる。
   - われわれの枠組みに限らない一般的な定理となる。principal_ideal_injectiveで証明済み。

## 半順序と極大元 (functionalPartialMaximal.lean)

- 極大要素はa < bならばb < aが成り立つものである。この性質を使って、同値類が極大でないところにあると、矛盾が生じる。

## 半順序が連結の場合

- 補題：サイズnの台集合の集合族で、半順序が定義されているとする。生成根付き集合のステムサイズは1で、親はたかだか1個で、パラレルな頂点はないとする。半順序の極大頂点は一つとすると、
- 極大頂点を通るhyperedgeは、たかだか1つである。
- 証明は、順序idealの定義から自明。極大な頂点が生成する単項idealがひとつ増えることになる。
- 補題：極大な頂点を集合族からdeletionしても、その頂点と関係ない部分の半順序関係は変わらない。よって、各頂点に関して、親はひとつであるような半順序がそのままのこる。
- 補題：上のセッティングで、極大な要素をdeletionした極大n-1の大きさの台集合を持つ集合族が平均rareであれば、もとの集合族も平均rareである。
  - 証明
  - 極大な頂点をdeletionすることでサイズn-1の集合族が得られる。極大な頂点を付け加えることで、元の順序idealに加えて、順序idealがちょうどひとつ付け加わる。
  - 証明は、付け加わった順序idealの大きさをkとすると、kはn以下で、頂点を付け加わることで、
  - 順序idealの大きさの和はkだけ増える。
  - 順序idealの個数は、ちょうど1増える。
  - 台集合の大きさは1増える。
  - よって、(順序idealの大きさの和*2-順序idealの個数*台集合の大きさ)は増えることはない。
  - sumを順序idealのもともとの和として、numを順序idealのもともとの個数として、num >= nであり、k <= nであるので、
  - 増加分は、((sum+k)*2 - (n+1)(num+1))-(2*sum - n*num) = 2k-n-num-1 <= 0である。
  - 証明終わり

## 半順序が連結でない場合
- まずは連結成分が2個の場合を考える。もしくは、頂点集合を2分割して、それぞれの間の頂点には大小関係がない場合を考える。
- 片方の順序idealの大きさの和をs1、順序idealの個数をh1、頂点集合の大きさをn1とする。
- もう片方の順序idealの大きさの和をs2、順序idealの個数をh2、頂点集合の大きさをn2とする。
- 合わせた半順序集合に関して順序idealの大きさの和は、s1*h2+s2*h1である。
- 合わせた半順序集合の順序idealの個数は、h1*h2である。
- 合わせた半順序集合の台集合の大きさは、n1+n2である。
- 平均rareであるためには、(s1*h2+s2*h1)*2-(h1*h2)*(n1+n2)<=0である。
- それぞれが平均rareなので、s1*2-h1*n1<=0, s2*2-h2*n2<=0であることからこれはいえる。
- 連結成分が3個以上の場合は、帰納法で証明することになる。
