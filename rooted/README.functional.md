# functional部分のREADME

- functionalで始まるファイル名は、functionalの定理を証明するためのファイルたちである。
- functionalMain.leanがメインのファイルであり、主定理が記述されている。他のファイルはその主定理のための補題である。
- このREADMEは、各ファイルに書いてある内容を解説している。

## 秋学期の言明 (functionalMain.lean内に記述。functionalCommon.leanの内容を利用)

- Vを有限台集合として、関数 f:V -> Vが定義する前順序を考える。v < f(v)というV上の2項関係が定義できる。この2項関係のtransitive closureを考えるとV上に前順序(preorder)が定義できる。この前順序に順序ideal全体を考えて、有限集合V上の集合族と思う。
- この集合族が平均rareであることを示すのがメイン定理。

```haskel
theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0
```

- 背景として、フランクルの予想は、平均rareのクラスに対しては反例がないということが知られているということがある。ここで考えているクラスに対しては、rareな頂点の存在が直接示すことができるので平均rareであることを示す必要はないが、平均rareであることを示すことができる。
- また、言明は単純ながら、証明を厳密に行おうとすると、そこそこ複雑なので、数学の定理としても興味深いものになっている。

## 前順序 (functionalCommon.lean)

- このファイルfunctionalCommonは、メイン定理を記述するために必要な定義と、それに関係する補題を記述している。
- fから導入される仮定をSetupというStructureにまとめる。Setupには、fやそれから導かれる前順序やSetoid(同値類)が定義されている。
- fで定義される前順序は、Setup.pre.leとなる。
- 頂点vからみて、f(v)を親と呼ぶ。Setup.pre.le v (f v)となる。
- vとf(v)は異なると仮定しても同じ場合を許しても、予想としては同値になる。とりあえず異なると仮定して考えている。s.valid.
- 補題：functionが与えられると、V上に前順序における頂点の同値類ができる。qClass_setup。
- この同値類に対して、setoidを考えることができる。Setup.setoid.
- ここまでの状況をSetupとして定義して、いろいろな言明の仮定として使っている。
- Setupの仮定のもとで、前順序に対するidealを考えている。idealは、集合族でいうhyperedgeである。
- fから前順序を定義する方法は、transitive closureを考えるルートと、vとf(v)の関係に両立する集合族から考えるルートの2通りがあって、それらは一致することも示している。le_eq_Rやpre_closuresystem_eq_lem。この定理は主定理の証明にも利用。
- 考える仮定Setupは、主定理の証明のために、このあと、一般化されたり特殊な場合に帰着されたりする。

## 前順序の性質 (functionalTreePreorder.lean)

- このファイルは、fから導かれるPreorder的な性質のまとめ。Commonを引き継ぐ内容。ファイル名は、Tree上の構造に前順序を定義するところからきている。
- fから前順序を定義する時に、idealを考えてから前順序を考える方法と2項関係を考えて、そのtransitive closureを考える方法がある。どちらでも同じ前順序が得られる。size_one_preorder_setup_lemma。内容的にはpre_closuresystem_eq_lemの内容と被る。
- 補題：前順序の大小関係と、親の関係で辿れるのは同値。f_and_pre, iteratef_lemma, iteratef_lemma_ref
- 補題：同値類の大きさが2以上のところはpreorderの極大要素である。eqClass_size_ge_two_implies_outside
- 補題：同値な要素の親は同値。f_on_equiv

## 同値類上の半順序の定義 (functionalTreePartialOrder.lean)

- fから導かれる同値類の上の半順序に関するファイル。同値類上で考えているので前順序ではなく、半順序になる。
- Setupの仮定のもと、頂点の同値類上に半順序が定義できる。半順序関係の定義は、同値類Aから同値類Bに順序の大小があることを、任意の順序idealに対して、同値類Aを含んでいるならば同値類Bを含んでいるということと、定義する。partialOrder_from_preorder
- この枠組みをSetup2としている。仮定としての強さは、Setupと同じ。半順序はfから決定するのでSetupから同値類上の半順序も決まる。Setup2.po.le。
- この2項関係は、半順序の公理を満たす。partialOrder_from_preorder
- preorderとsetoid上のpartialOrderの関係を色々示す。pullback_preorder_lemma. pushforward_preorder_lemma
- setoidの要素の極大性is_MaximalQも定義して、preorderの極大性との関係を示す。isMaximal_iff
- fの同値類版が、fqという関数。Setup2.fq。
- fとfqの関係も示す。f_on_equiv_n.
- fq単独の性質も示す。fqで辿れることと、半順序の関係。fq_lemma。fq_lemma_rev。reach_po_leq

## 同値類上の半順序が作る集合族 (functionalSPO.lean)

- このファイルは、Setup_spoという同値類上の半順序に関する仮定に関するもの。traceの話が入っていたり、やや内容が散漫。Setup_spoは、Setup2よりも一般化されている。
- 前順序を前提にしないSetoid上の半順序を抽象化した仮定がSetup_spo2。Setup_spoは極大なところ以外は同値類の大きさが1であるというsingleton_if_not_maximalの仮定を外したもの。とりあえず、この仮定はしばらく使わないので。
- validの仮定があると、極大な同値類の大きさが1にならないが、Setup_spoやSetup_spo2の仮定においては、極大な部分の同値類の大きさは1になりうる。仮定の種類が無駄に増えている気もするので、validの仮定なしで元の言明を書き直した方がいいのかも。
- 与えられた要素が属する同値類を与える関数classOfを定義している。Setup_spo前提。
- Setup_spoとreachの関係についても補題を示している。reach_leqとreach_leq_rev。
- Setup_spoとSetup2の関係なども示す。
- パラレルな頂点をtraceした集合族もこれにより、前順序を定めることができる。サイズ2以上の同値類から同値な頂点をひとつtraceしても、半順序の親がたかだか1つということも変わらない。

## spoのtrace (functionalSPOtrace.lean)

- Traceする前(大きい世界)とTraceしたあと(小さい世界)間の写像。要素間のものと、同値類間のもの。いろいろな補題を示す。
- restrictedSetoidは、xによるtraceのsetoid間の対応。
- 補題: パラレルな頂点をtraceした場合、もとの前順序で大小関係があることと、traceした集合族での大小関係は一致する。ここでの大小関係は、hyperedgeがxを含んでいたらyも含むという関係。setup_trace_reach
- Setup_spoから得られるideal全体の集合族において、同値類の大きさが2以上のときに、1元traceしても、またSetup_spoになる。setup_trace

## 同値類上の半順序 (functionalSPO2.lean)

- Setup_spoからsingleton_if_not_maximalの仮定をつけたのがSetup_spo2。それに関するファイル。
- MainのファイルではSetup_spoではなく、Setup_spo2を利用する。
- V上に同値類が与えられていて、以下の条件を満たすとする。1. サイズ2以上の同値類は、半順序の極大な要素のみ。2. 半順序の親は、たかだか1つ。
- この半順序に対して、順序idealを考えて、hyperedgeと思って、集合族を考えることができる。
- 補題：サイズが2以上の同値類は、半順序の極大要素に対応するところにしか出てこない。<=eqClass_Maximalが言明。setup2_induces_spoで利用。
- 補題：大小関係があるときは、traceしても大小関係がある。setup_trace_spo_le
- 補題：サイズ2以上の同値類からパラレルな頂点をひとつtraceしても、サイズが2以上の同値類が極大なものに限られることも変わらない。つまり、またSetup_spo2になる。setup_trace_spo2の定義。

## 同値類上の半順序が作る集合族 (functionalTreeIdeal.lean)

- 順序から決まるidealの定義やその性質。
- pre_closuresystemは、前順序から作ったideal。
- pre2_closuresystemは、Setup2のpoを利用して作ったideal。
- 補題：hyperedgeの集合の全体(=前順序の順序ideal全体)は、この半順序の順序idealに一致する。Preorder_eq_PartialOrder
- spo_closuresystemは、Setup_spoの仮定から作ったideal。
- 補題：spo_closreusystemは、pre2_closuresystemと一致する。Setup_spo_eq_PartialOrder 

## 順序idealと平均rare (functionalIdealRare.lean)

- 順序idealとは、考えている前順序で、下に閉じている集合のことである。
- 頂点集合上に前順序が与えられると順序idealの全体が決まる。これは集合族のhyperedgeと思って、平均rareになるかなどが議論できる。
- 平均rareとは、(順序idealの大きさの和*2-順序idealの個数*台集合の大きさ)<=0のことである。
- 補題: Setup_spo2の仮定のもと、サイズ2以上の同値類の頂点は、rareな頂点になる。spo2_rareで証明している。
- ここで、Setup_spo2の仮定を利用している。

## 半順序のtrace (functionalTraceIdeal.lean)

- 同値な頂点(パラレルな頂点とも呼ぶ)のひとつをtraceすることにより、同一視していく方向性。
- 集合族としては、パラレルな頂点を持つ頂点をtraceしていくことにより、パラレルな頂点を持たない集合族を得ることができる。
- traceしたものと、集合族が等しければ、ndsも等しい。Setup_spoの仮定。theorem trace_ideal_nds 
- excessもここで定義。
- traceすることで、excessはひとつ減る。Setup_spoの仮定でもよいかも。trace_excess_decrease

## 半順序のtrace (functionalTraceIdeal2.lean)

- 半順序の構造Setup_poとの橋渡しの部分。
- 同値類の大きさが全部1であれば、Setup_poとみなせるということを示すのがメイン。
- trace_ideal_nds_increaseのところで、Setup_spo2の仮定を使っている。
- spo2_rareを呼んでいて、これがSetup_spo2の仮定を使っている。
- Setup_spo2の仮定は、同値類の大きさが1であることを仮定しているので、traceした後の集合族は、同値類の大きさが1であることがわかる。
- 補題： 集合族に対して、パラレルな要素を持つ要素で、rareな頂点をtraceして平均rareであれば、もともと平均rareである。 trace_ideal_nds_increase2
  - この補題は順序とは関係なく、一般に成り立つ。
- この補題の証明は、すでにParallel.leanのファイルの中で完了している。しかし、それを利用して証明しているわけではない。
- 半順序に対するidealの定義も。po_closuresystem

## Mainの中の補題 (functionalMain.lean)

- functionalMainの中で大枠の議論をしている。
- 補題: 集合族に対して、パラレルな要素を持つものが平均rareであることを示すためには、サイズ2以上の同値類をすべて1頂点にまでtraceしたものが平均rareであることを示せば良い。setup_spo2_average_rare
- パラレルな頂点の個数に関する帰納法で示すことができる。サイズがkの同値類があれば、k-1を足すということでbase caseが0にするとよい。

## 半順序の平均rare (functionalPartialTrace.lean)

- ここまでで、サイズ2以上の同値類はないと仮定してよくなったので、同値類のサイズは全部1で、頂点集合ground上の半順序と思うことができる。
- パラレルな頂点がなくなったあとは、グラフ論の森(forest)で各連結成分に根が指定されているものと思うことができる。根から遠い頂点が下となる。
- 全体的な流れはMainに書いてある。
- パラレルな頂点がなくなったあとは、極大な頂点(=グラフの根)をdeletionしていく。集合族としては、根のdeletionと考えても、traceと考えても同じ。po_trace。
- 極大な頂点を集合族からtraceしても、その頂点と関係ない部分の半順序関係は変わらない。
 
## 連結成分が1つの半順序 (functionalPartialOne.lean)

- コンポーネントの数が1だと、極大要素を含むhyperedgeが全体集合になること。
- 補題：サイズnの台集合の集合族で、半順序が定義されているとする。生成根付き集合のステムサイズは1で、親はたかだか1個で、パラレルな頂点はないとする。半順序の極大頂点は一つとすると、 極大頂点を通るhyperedgeは、たかだか1つである。component_one
- 補題：半順序集合の順序idealの個数は、台集合の数よりも同じか多い。
  - これは、各要素を単項idealに対応させれば、それが単射になることからわかる。反対称律から、単射でなければパラレルな要素が出てくる。
  - われわれの枠組みに限らない一般的な定理となる。principal_ideal_injectiveで証明。
- traceすると、normalized_Degree_sumが減ることはない。normalized_degree_sum_gt
- 補題：連結成分が1つであるときに、極大な要素をtraceした極大n-1の大きさの台集合を持つ集合族が平均rareであれば、もとの集合族も平均rareである。これはMainのS  etup_po_average_rare_card_oneで示されている。

## 半順序の極大要素に対する補題 (functionalPartialMaximal.lean)

- Setup po前提の極大元に関する部分。極大であるという述語はpo_maximal。
- 極大要素に関する色々な補題を証明。
- po_maximal_lem: poに関する極大性の補題。極大であることと、s.fが自分自身に移ることが同値。
- かならず上に極大要素がある。lemma po_maximal_reachable 
- 任意の要素を極大要素は、ただ1つしかない。po_maximal_reachable_eq 
- proj_maxは、本当に極大元になっていることの証明。proj_max_maximal
- setroidのコンポーネントが等しいことと、極大要素が等しいことは同値。proj_max_quotient

## 半順序が連結でない場合 (functionalDirectProduct.lean, functionalDirectProduct2.lean)

- 連結成分が2個以上の場合を考える。numClassesが同値類の個数。
- 同値類の一つをqとして、qの側とq以外の部分に分割。
- directProduct_ndsが目標。直積でかけるときに、両方とも非正であれば、直積も非正になる。

