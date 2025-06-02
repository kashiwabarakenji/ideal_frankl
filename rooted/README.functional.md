# functional部分のREADME

- functionalで始まるファイル名のファイル群は、この研究の主定理であるfunctionalの定理を証明するためのファイルたちである。
- functionalMain.leanがメインのLeanファイルであり、主定理が記述されている。他のファイルはその主定理の証明のための補題である。
- functionalで始まらないファイル名は、一般的な閉集合族に関する補題を集めたものであり、今回の定理の証明に利用されるものも存在する。
- このREADME.functionalは、各functionalのLeanファイルに書いてある内容を解説している。主にそのファイル外から引用される補題(privateでない補題)を中心に解説している。

## 主定理の言明 (functionalMain.lean内に記述)

- Vを有限台集合として、関数 f:V -> Vが定義する前順序を考える。v < f(v)というV上の2項関係が定義できる。この2項関係のtransitive closureを考えるとV上に前順序(preorder)が定義できる。この前順序に順序ideal全体を考えて、有限集合V上の集合族と思う。
- 主定理: 集合族は平均rareとなる。

```haskel
theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0
```
- 言明自体はfunctionalMainに記述されているが、functionalCommon.leanの内容を利用している。
- 平均rareとは、集合族の標準化次数和(normalized_degree_sum)が非正であることをいう。
- 標準化次数和とは、集合族のhyperedgeの大きさの和から、hyperedgeの個数と台集合の大きさを掛けたものを引いた値である。

## 主定理の背景

- 標準化次数和が非正であるとき、rareな頂点が存在することが知られている。
- 平均rareのクラスに対してはrareな頂点が存在するので、このクラスにはフランクルの予想の反例がないということが簡単にわかる。
- ここで考えている集合族のクラスに対しては、rareな頂点の存在が直接示すことができるので平均rareであることを示す必要はないが、本定理によって平均rareであることを示すことができる。
- 全体集合を持つ、共通部分で閉じた集合族は閉集合族と呼ばれ、根つき集合族で表すことができる。
- 共通部分で閉じた集合族を根つき集合で表したときに、根がない頂点は、そもそもrareになることが簡単にわかる。すると、各頂点に対して、表現の中のある根つき集合が存在して、その頂点に根がある場合のみを考えればいいことがわかる。
- 根付き集合は、根となる頂点xとステムと言われる集合Aのペア(A,x)からなって、ステムは根を含まない。根付き集合の集まりが与えられたたら、ステムAを含む集合は必ずxを含むというルールで、集合族ができる。この集合族が共通部分で閉じていて、全体集合も持つ。閉集合族と呼ばれる。

## 主定理の意味

- 各頂点が根を持たない一般の場合を考えるのは難しい(フランクルの予想そのもの)ので、根つき集合族の生成集合において、各頂点に対して、根がそれぞれ一個だけの場合を考える。さらにステムの大きさも1に限定したときに、idealが作る集合族が平均rareであることを示したいというのが、主定理の内容である。
- 主定理の言明は単純ながら、証明を厳密に行おうとすると、そこそこ複雑であり、数学の定理としても興味深いものになっている。Lean 4の証明は1万行程度ある。
- 定理の証明において、頂点上に半順序関係が存在する時に、そのidealの集合族が平均rareであることの証明に帰着される。
- つまり次の準主定理を証明することで、主定理の証明ができる。準主定理もそれ自体数学的に興味がある言明になっている。
- 準主定理(setup_po_average_rare)：頂点上に親がたかだか一つしなかい半順序関係が存在する時に、そのidealの集合族は平均rareである。
- このときは、極大頂点を考えれば、rareであることは簡単であるし、知られている。しかし、idealの集合族が平均rareであることは、私の知る限り知られてないというか議論されていないと思われる。
- なお、ステムの大きさが2以上を許した場合に関しては、成り立つのか成り立たないのか未解決である。

## 主定理の証明の概略 (functionalMain.lean)

- 主定理は、もともとの枠組みがSetupという形で設定され、それが一般化されて、Setup_spo2となる。それが特定のケースに帰着されて、Setup_poとなる。
- 証明上の論理的な順番としては、setup_po_average_rareが証明されて、setup_spo2_average_rareが証明されて、メインであるSetup_average_rareが証明される。functionalMain.leanの中の順番でもそうなっている。
- しかし、このREAMEのなかのファイルの順番では、Setup_average_rareの補題のファイル群、setup_spo2_average_rareの補題のファイル群、setup_po_average_rareの補題のファイル群という順番で説明している。
- 主定理の言明 (Setup_average_rare)
  - 頂点集合V上にfから導入される前順序と、それから導かれる同値類を考える。Setupの枠組み。
  - この同値類上に半順序を定義する。fから導入される同値類上の半順序を考える。このidealが平均rareであることが主定理。
- 主定理の枠組みは、以下のように抽象化できる。(Setup_spo2の枠組み)
  - 補題(setup_spo2_average_rare)：同値類上の半順序で親がたかだか1つで、同値類が大きさ2以上が極大要素に限られる場合の半順序は、平均rareである。
- これは、以下のケースに帰着される。(Setup_poの枠組み)
  - 準主定理(setup_po_average_rare):頂点上に親がたかだか一つしかない半順序が与えられたときのidealの集合族を考える。idealは、集合族のhyperedgeと考える。このidealは平均rareである。
  - この証明は、極大な頂点をtraceすることにより、頂点数に関する帰納法で証明する。連結成分の数が2以上かどうかで分けて議論する。

## Setupの仮定についてのまとめ

- もともとの主定理の仮定は、Setup。validなfが与えられたという条件と同じ。おまけでfから導かれる前順序や、同値類が定義されている。
- Setup2は、Setupの仮定を引き継いで、同値類上に半順序が定義されるという仮定を追加したもの。Setup2の仮定としての強さは、Setupと同じ。
- Setup_spoは、Setupを抽象化したもの。前順序からでなく、同値類からスタートしているので抽象化している。Setup_spoはSetup2から極大なところ以外は同値類の大きさが1であるというsingleton_if_not_maximalの仮定を外したもの。とりあえず、この仮定は多くの補題で使わないので、簡単化のために外している。
- Setup_spo2は、大きさ2以上の同値類は極大元に限るという条件singleton_if_not_maximalを追加したもの。前順序から作った同値類はこの条件を満たすが、多くの議論では、Setup_spoで十分のために、分離されている。Setup_spoとSetup_spo2の仮定は同値ではない。
- Setup_poは、Setup_spoで同値類の大きさが全部1であるときと実質的に同等。つまり、親がたかだか1つであるような半順序が与えられているという仮定。

# Setup_average_rareのための補題のファイル群

## 前順序の導入 (functionalCommon.lean)

- ファイルの概要
  - このファイルfunctionalCommonは、メイン定理を記述するために必要な定義と、それに関係する補題を記述している。
  - ファイル名がCommonとなっているが、現状で共通に必要な内容は多くなく、Setup前提の議論が中心である。
- ファイルの仮定
  - fから導入される仮定をSetupというStructureにまとめる。
  - Setupには、fやそれから導かれる前順序やSetoid(同値類)が定義されている。
  - fで定義される前順序は、Setup.pre.leとなる。
  - 頂点vからみて、f(v)を親と呼ぶ。Setup.pre.le v (f v)となる。
  - ここで導入される前順序は、親がひとつしかない特殊な前順序ということになる。
  - vとf(v)は異なると仮定(s.valid)しても同じ場合を許しても、言明としては同値になる。とりあえず異なると仮定して考えている。 
  - 考える仮定Setupは、主定理の証明のために、このあと、一般化されたり特殊な場合に帰着されたりする。
- ファイルの各内容 
  - 定義size_one_preorder: function fが与えられると、前順序が定まる。
  - setoid_preorder: 前順序から導かれる頂点の同値類(setoid)。
  - eqClass_setup: 与えられた頂点と同値な頂点の全体。
  - 補題(eqClass_eq)：前順序で同値であることと、eqClassで同値であることが必要十分。
  - Setupの仮定のもとで、前順序に対するidealを考えている(pre_closuresystem)。idealは、集合族でいうhyperedgeである。
  - fから前順序を定義する方法は、親子関係のtransitive closureを考えるルートと、vとf(v)の関係に両立する集合族から考えるルートの2通りがあって、それらは一致することも示している。le_eq_Rやpre_closuresystem_eq_lem。この定理は主定理の証明にも利用。
  

## 前順序の性質 (functionalTreePreorder.lean)

- このファイル(functionalTreePreorder.lean)は、fから導かれるPreorder的な性質の補題。Commonを引き継ぐ内容。
- ファイル名は、前順序を定義してTree上の構造を作ることからきている。
- fから前順序を定義する時に、両立するidealを考えてから前順序を考える方法と、fの2項関係を考えてそのtransitive closureから定義する方法がある。どちらでも同じ前順序が得られる。size_one_preorder_setup_lemma。内容的にはpre_closuresystem_eq_lemの内容と被る。
- 補題：前順序の大小関係と、親の関係で辿れるのは同値。f_and_pre, iteratef_lemma, iteratef_lemma_ref
- 補題：同値類の大きさが2以上のところはpreorderの極大要素である。eqClass_size_ge_two_implies_outside
- 補題：同値な要素の親は同値。f_on_equiv

## 同値類上の半順序の定義 (functionalTreePartialOrder.lean)

- このファイルfunctionalTreePartialOrder.leanはfから導かれる同値類の上の半順序に関するもの。同値類上で定義されているので前順序ではなく、半順序になる。
- 同値類上の半順序とSetup2
  - 考えている仮定は、引き続きSetup。Setupの仮定のもと、頂点の同値類上に半順序が定義できる。半順序関係の定義は、同値類Aから同値類Bに順序の大小があることを、任意の順序idealに対して、同値類Aを含んでいるならば同値類Bを含んでいるということと、定義する。
  - この半順序の枠組みをSetup2としている。仮定としての強さは、Setupと同じ。半順序はfから決定するのでSetupから同値類上の半順序も決まる。Setup2.po.le。
  - この2項関係Setup2.po.leは、半順序の公理を満たす。partialOrder_from_preorder
  - preorderとsetoid上のpartialOrderの関係を色々示す。
  - fから定義された前順序と同値類上の半順序の関係は pullback_preorder_lemma. pushforward_preorder_lemma という補題で示される。
- 極大性
  - setoidの要素の極大性is_MaximalQも定義する。
  - preorderの極大性との関係を示す。isMaximal_iff
- 親関数
  - 親指定関数fの同値類版が、fqという関数。Setup2.fq。
  - fとfqの関係も示す。f_on_equiv_n.
  - fq単独の性質も示す。fqで辿れることと、半順序po.leの関係。fq_lemma。fq_lemma_rev。reach_po_leq

## 同値類上の半順序が作る集合族 (functionalSPO.lean)

- 概要
  - このファイルは、Setup_spoという同値類上の半順序に関する仮定に関する補題を集めたもの。
  - Setup_spoは、Setup2よりも一般化されている仮定。spoは、fや前順序からスタートするのではなく、setoid上の同値類からスタートしている。
  - 前順序を前提にしないSetoid上の半順序を抽象化した仮定がSetup_spo2。これは、SPO2のファイルで出てくる。
  - validの仮定があると、極大な同値類の大きさが1にならないが、Setup_spoやSetup_spo2の仮定においては、極大な部分の同値類の大きさは1になりうる。仮定の種類が無駄に増えている気もするので、validの仮定なしで元の言明を書き直した方がいいのかも。
  - このファイルの補題は、Setup_average_rareの証明にも、Setup_spo2_average_rareの証明にも利用される。
- ファイルの内容
  - 与えられた要素が属する同値類を与える関数classOfを定義している。Setup_spo前提。
  - Setup_spoとreachの関係についても補題を示している。reach_leqとreach_leq_rev。
  - Setup_spoとSetup2の関係なども示す。
  - パラレルな頂点をtraceした集合族もこれにより、前順序を定めることができる。サイズ2以上の同値類から同値な頂点をひとつtraceしても、半順序の親がたかだか1つということも変わらない。

## 同値類上の半順序が作る集合族 (functionalTreeIdeal.lean)

- このファイルは、順序idealが作る集合族に関する定義や補題を集めたものである。
- 順序idealとは、考えている前順序で、下に閉じている集合のことである。順序idealの定義やその性質。
- pre_closuresystemは、前順序から作ったideal。Commonで定義済み。
- pre2_closuresystemは、Setup2のpoを利用して作ったideal。
- 補題(Preorder_eq_PartialOrder)：hyperedgeの集合の全体(pre_closuresystem)は、この半順序の順序ideal(pre2_closuresystem)に一致する。仮定はSetup2。
- spo_closuresystemは、Setup_spoの仮定から作ったideal。functionalIdealRare.leanなどからも参照される。
- 補題(Setup_spo_eq_PartialOrder)：spo_closuresystemは、pre2_closuresystemと一致する。
- Setup_spoのidealに関する補題は、特にtraceに関するものなどは、functionalTraceIdeal.leanやfunctionalTraceIdeal2.leanに記述されている。これも仮定はSetup2。

# setup_spo2_average_rareの証明のための補題のファイル群

基本的に仮定はSetup_spoかSetup_spo2である。この補題に帰着させる部分で、Setup2の仮定を使うこともある。

## spoのtrace (functionalSPOtrace.lean)

- このファイルは、頂点数の帰納法を考えるためにパラレルな頂点のtraceを考える際の準備の補題を記述している。
- 仮定としては、Setup_spoを考える。
- restrictedSetoidは、xによるtraceのsetoid間の対応。
- Traceする前(大きい世界)とTraceしたあと(小さい世界)間の写像を定義する。
- 要素間の写像(toErased)と、それに関する性質。同じ同値類の要素はtraceで同じ同値類に移る。toErased_eq
- 同値類間のもの(toOld,toNew)。toOldとtoNewが、逆写像の関係になっていることも示す。NewOld_idとOldNew_id。
- 補題(setup_trace_reach): パラレルな頂点をtraceした場合、もとの前順序で大小関係(reach)があることと、traceした集合族での大小関係は一致する。ここでの大小関係は、hyperedgeがxを含んでいたらyも含むという関係。
- 定義(setup_trace): Setup_spoから得られるideal全体の集合族において、同値類の大きさが2以上のときに、1元traceしても、またSetup_spoになる。
- 補題(toNew_classOf):xを含まない同値類は、traceしても大きさが変わらない。

## 同値類上の半順序 (functionalSPO2.lean)

- 概要
  - Setup_spoからsingleton_if_not_maximalの仮定をつけたのがSetup_spo2。それに関するファイル。
  - functionalMainのファイルではSetup_spoではなく、Setup_spo2を利用する。
  - Setup_spo2の仮定をまとめると、V上に同値類が与えられていて、以下の条件を満たすとする。1. サイズ2以上の同値類は、半順序の極大な要素のみ。2. 半順序の親は、たかだか1つ。
  - この半順序に対して、順序idealを考えて、hyperedgeと思って、集合族を考えることができる。
- ファイルの内容 仮定がSetup2
  - 仮定はSetup2だが、Setup_spo2が出てくるものもここにある。これは主定理の証明に使われる。
  - 補題(eqClass_Maximal)：サイズが2以上の同値類は、半順序の極大要素に対応するところにしか出てこない。setup2_induces_spoで利用。この部分は仮定はSetup2であり、主定理の証明で利用。
  - 定義(setup2_induces_spo)は、仮定がSetup2で、Setup_spo2に埋め込めるというもの。
- ファイルの内容 仮定がSetup_spo2。
  - 補題(setup_trace_spo_le)：大小関係があるときは、traceしても大小関係（spo_le）がある。
  - 定義(setup_trace_spo2)：サイズ2以上の同値類からパラレルな頂点をひとつtraceしても、サイズが2以上の同値類が極大なものに限られることも変わらない。つまり、またSetup_spo2になる。


## 順序idealと平均rare (functionalIdealRare.lean)

- このファイルでの補題の仮定は、Setup_spoが多いが、追加でMaximalを仮定しているので実質的にSetup_spo2の仮定を使っている。そとから参照されるspo2_rareは、Setup_spo2の仮定を使っている。
- 頂点集合上に前順序が与えられると順序idealの全体が決まる。これは集合族のhyperedgeと思って、平均rareになるかが議論できる。
- 平均rareとは、標準化次数和が非正(順序idealの大きさの和*2-順序idealの個数*台集合の大きさ)<=0のことである。
- 補題(spo2_rare): Setup_spo2の仮定のもと、サイズ2以上の同値類の頂点は、rareな頂点になる。
- ここで、Setup_spo2の仮定を利用している。

## 半順序のtrace (functionalTraceIdeal.lean)

- 概要
  - 同値な頂点(パラレルな頂点とも呼ぶ)のひとつをtraceして減らすことにより、同一視していく方向性。
  - 基本的にSetup_spoの仮定で考えている。
  - 集合族としては、パラレルな頂点を持つ頂点をtraceしていくことにより、パラレルな頂点を持たない集合族を得ることができる。この議論自体はMainで行なっている。ここではその準備。
- ファイルの内容 Setup_spoの仮定  
  - 定理(trace_ideal_nds ):traceしたものと、集合族が等しければ、標準化次数和ndsも等しい。
- ファイルの内容 Setup_spo2の仮定
  - 補題(trace_ideal_nds_increase2)： 集合族に対して、パラレルな要素を持つ要素で、rareな頂点をtraceして平均rareであれば、もともと平均rareである。 
  - この補題は順序構造とは関係なく、一般に成り立つ。
  - この補題の証明は、すでにParallel.leanのファイルの中で完了している。しかし、ここではそれを利用して証明せずに、改めて独自に証明している。
  - spo2_rareを呼んでいて、これがSetup_spo2の仮定を使っている。
  
## 同値類の大きさのexcess (functionalExcess.lean)

- excessをここで定義。excessは、同値類の大きさがすべて1であるときを0として、それからパラレルな要素があるたびに1ずつ増加していく関数。
- 補題(trace_excess_decrease):traceすることで、excessはひとつ減る。Setup_spoの仮定でもよいかも。
- 補題(excess_zero): excessは0であれば、同値類の大きさがすべて1。  
- 補題(exists_q_card_ge_two_of_excess_pos): excessが正ならば、大きさ2以上の同値類が存在。
- Mainで使っている。

## 半順序のtrace (functionalPartial.lean)

- 概要
  - Mainにあるsetup_po_average_rareへの帰着に必要な補題を証明。
  - 同値類の大きさが全部1であれば、Setup_poとみなせるということを示すのがこのファイルの主要な結果。
  - ファイルの内容
    - Setup_poの定義を行なっている。この前提は、親をたかだか一つしか持たない、半順序という前提。
    - Setup_poの半順序に対するidealの定義po_closuresystemもここで行なっている。
    - 定義 (po_ideal_system_from_allone)は、Setup_spoのidealは、すべての同値類の大きさが1であるときに、すべての要素を含むidealになることを示す。


## Mainの中の補題 (functionalMain.lean)

- functionalMainの中で大枠の議論をしている。
- setup_average_rareがSetupの仮定を使って書いたメイン定理。
- 今まで証明したことであるPreorder_eq_PartialOrderとSetup_spo_eq_PartialOrderを利用して、setup_spo2_average_rareの仮定のもと、メイン定理は証明される。つまり、Setup前提のaverage rareの定理をSetup_spo2前提のaverage rareの定理に帰着している。setup_spo2_average_rare
- 定理(setup_spo2_average_rare)：同値類上の半順序が与えられていて、同値類の大きさが2以上なのは、極大なものに限る場合は、平均rareになる。
- 補題(trace_ideal_nds_increase2): 集合族に対して、パラレルな要素を持つものが平均rareであることを示すためには、サイズ2以上の同値類をすべて1頂点にまでtraceしたものが平均rareであることを示せば良い。setup_spo2_average_rareの証明でこの言明を利用。
- setup_spo2_average_rareはパラレルな頂点の個数に関する帰納法で示すことができる。excessの値でパラレルな頂点の個数を表す。すべての同値類の大きさが1であれば、excessの値は0である。
- 補題setup_po_average_rareの部分は後述。

# setup_po_average_rareの証明のための補題のファイル群

基本的に仮定は、Setup_poである。

## 半順序の平均rare (functionalPartialTrace.lean)

- ここまでで、サイズ2以上の同値類はないと仮定してよくなったので、同値類のサイズは全部1で、頂点集合ground上の半順序と思うことができる。
- パラレルな頂点がなくなったあとは、グラフ論の森(forest)で各連結成分に根が指定されているものと思うことができる。根から遠い頂点が下となる。
- Mainにあるsetup_po_average_rareを示すのがここからの目標。
- 全体的な流れはMainに書いてある。setup_spo2_average_rare
- 極大な頂点を集合族からtraceしても、その頂点と関係ない部分の半順序関係は変わらない。
 
## 連結成分が1つの半順序 (functionalPartialOne.lean)

- コンポーネント(連結成分)の数が1だと、極大要素を含むhyperedgeが全体集合になること。
- 補題：サイズnの台集合の集合族で、半順序が定義されているとする。生成根付き集合のステムサイズは1で、親はたかだか1個で、パラレルな頂点はないとする。半順序の極大頂点は一つとすると、 極大頂点を通るhyperedgeは、たかだか1つである。component_one
- 補題：半順序集合の順序idealの個数は、台集合の数よりも同じか多い。
  - これは、各要素を単項idealに対応させれば、それが単射になることからわかる。反対称律から、単射でなければパラレルな要素が出てくる。
  - われわれの枠組みに限らない一般的な定理となる。principal_ideal_injectiveで証明。
- 補題(normalized_degree_sum_gt):連結成分が1つの場合、極大要素をtraceすると、normalized_Degree_sumが減ることはない。
- 補題：連結成分が1つであるときに、極大な要素をtraceした極大n-1の大きさの台集合を持つ集合族が平均rareであれば、もとの集合族も平均rareである。これはMainのSetup_po_average_rare_card_oneで示されている。

## 半順序の極大要素に対する補題 (functionalPartialMaximal.lean)

- Setup po前提の極大元に関する部分。極大であるという述語はpo_maximal。
- 極大要素に関する色々な補題を証明。
- po_maximal_lem: poに関する極大性の補題。極大であることと、s.fが自分自身に移ることが同値。
- かならず上に極大要素がある。lemma po_maximal_reachable 
- 任意の要素を極大要素は、ただ1つしかない。po_maximal_reachable_eq 
- proj_maxは、本当に極大元になっていることの証明。proj_max_maximal
- setroidのコンポーネントが等しいことと、極大要素が等しいことは同値。proj_max_quotient

## 半順序が連結でない場合の補題部分 (functionalDirectProduct.lean, functionalDirectProduct2.lean)

- 連結成分が2個以上の場合を考える。numClassesが同値類(連結成分)の個数。
- 同値類の一つをqとして、連結成分が2以上の場合に、qの側とq以外の部分に分割。
- qの側がcomp、q以外の部分がexclと名前がついている。
- 半順序をqを含む部分とqを含まない部分に分けて考える。
- functionalDirectProductは、compとexcelのそれぞれの側に関して、Setup_poを定義できる。
  - comp_poとexcl_po
- 以下、functionaDirectProduct2.leanの内容。
- directProduct_comp_excel_ground_cとdirectProduct_comp_excel_ground_eで、台集合が真に小さくなっていることを示している。
- 補題(directProduct_nds):集合族がqを含む部分と含まない部分の直積でかけるときに、normalized_degree_sumが両方とも非正であれば、直積も非正になる。

## 半順序の平均rare (functionalMain.leanの一部)

- Mainのファイルで、setup_po_average_rareとして半順序に関する準主定理を頂点数に関する帰納法で証明する。
- ベースケースは、頂点数が1のとき。これは、etup_po_average_rare_card_oneで証明。
- 帰納ケースは、強い再帰法を用いる。
- 連結成分が一つしかない場合は、極大要素をtraceする。
- 連結成分が複数ある場合には、直積分解を用いる。
- この場合も、連結成分の頂点数は、考えている頂点数よりも少ないので帰納法的に平均rareが成り立つとして良い。
- 平均rare同士の直接は、平均rareということを、directProduct_ndsで証明済み。

## 全体的なリファクタリング予定のまとめ

- 主定理からvalidの条件をなくす。
- functionalCommon.leanは、内容的にcommonというより、Setup前提の主定理のための定義だがどうするか。 
  - ファイルの名前を変える？他にもTreePreorderなどの名前も変えた方がいいか。
- ファイル名の統一が取れていない。Mainのファイルの定理のどの定理から引用されるかでファイルをわけるといいかも。Mainにある補題名を変えて、それに合わせてファイル名を整理するのがいいか。もしくは、引用場所よりも仮定で分けた方がわかりやすいかもしれない。枠組みごとになるので。
- pre_closuresystem_eq_lemの証明内容の重複。
- functionalTreePreorder.leanでreachを使った表現に書き換える。
- Setup2を無くして、Setupに関数を定義する。Setup_spo2などの名前も変える。同値なので。
- 全体的にSetupなどの仮定に依存する部分を減らして、部品を共通化したい。今は枠組みごとに独立に議論をしている。たとえば、qClassとclassOfは、同値類を与えるという同じ目的で定義されているが、枠組みごとに定義されている。setoidが与えられれば、定義できるはず。
- iteratef_lemma, iteratef_lemma_refなど片側ずつになっている定理を必要十分の形に書き直す。

- 論文を書いた後に、全面的に書き直すか？別のリポジトリにするのか？それだと大変すぎるかも。

