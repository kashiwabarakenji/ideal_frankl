# functional部分のREADME

- functionalで始まるファイル名のファイル群は、この研究の主定理であるfunctionalの定理を証明するためのファイルたちである。
- functionalMain.leanがメインのLeanファイルであり、主定理が記述されている。他のファイルはその主定理のための補題である。
- このREADMEは、各ファイルに書いてある内容を解説している。主にファイル外から引用される内容を中心に解説している。

## 主定理の言明 (functionalMain.lean内に記述。functionalCommon.leanの内容を利用)

- Vを有限台集合として、関数 f:V -> Vが定義する前順序を考える。v < f(v)というV上の2項関係が定義できる。この2項関係のtransitive closureを考えるとV上に前順序(preorder)が定義できる。この前順序に順序ideal全体を考えて、有限集合V上の集合族と思う。
- この集合族が平均rareであることを示すのがメイン定理。

```haskel
theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0
```

- 背景として、フランクルの予想は、平均rareのクラスに対してはrareな頂点が存在するので、反例がないということが簡単にわかるということがある。ここで考えている集合族のクラスに対しては、rareな頂点の存在が直接示すことができるので平均rareであることを示す必要はないが、本定理によって平均rareであることを示すことができる。
- 共通部分で閉じた集合族は根つき集合族で表すことができる。共通部分で閉じた集合族を根つき集合で表したときに、根がない頂点は、そもそもrareになることが簡単にわかる。すると、各頂点に対して、表現の中のある根つき集合が存在して、その頂点に根がある場合のみを考えればいいことがわかる。
- その一般の場合を考えるのは難しい(フランクルの予想そのもの)ので、根つき集合族の生成集合において、各頂点に対して、根がそれぞれ一個だけの場合を考える。このときに、idealが作る集合族が平均rareであることを示したいというのが、主定理の内容である。
- 主定理の言明は単純ながら、証明を厳密に行おうとすると、そこそこ複雑なので、数学の定理としても興味深いものになっている。Lean 4の証明は1万行程度ある。
- 定理の証明において、頂点上に半順序関係が存在する時に、そのidealの集合族が平均rareであることの証明に帰着される。
- 準主定理(setup_po_average_rare)：頂点上に半順序関係が存在する時に、そのidealの集合族は平均rareである。
- このときは、極大頂点を考えれば、rareであることは簡単であるし、知られている。しかし、idealの集合族が平均rareであることは、私の知る限り知られてないと思われる。

## 全体の証明の概略 (functionalMain.lean)

- 主定理の証明は、以下のような流れで行われる。
  - 頂点集合V上にfから導入される前順序と、それから導かれる同値類を考える。
  - 同値類上に半順序を定義する。fから導入される同値類上の半順序を考える。このidealが平均rareであることが主定理。
  - 抽象化して、
  - 補題(setup_average_rare)：親がたかだか1つで、同値類が大きさ2以上が極大要素に限られる場合の半順序は、平均rareであることを示す。
  - これは、以下のケースに帰着される。
  - 頂点上に半順序が与えられたときのidealの集合族を考える。idealは、集合族のhyperedgeと考える。このidealは平均rareであることを示す。(上の準主定理) 。
  - この証明は、極大な頂点をtraceすることにより、頂点数に関する帰納法で証明する。連結成分の数が2以上かどうかで分けて議論する。


## 前順序の導入 (functionalCommon.lean)

- ファイルの概要
  - このファイルfunctionalCommonは、メイン定理を記述するために必要な定義と、それに関係する補題を記述している。
  - ファイル名がCommonとなっているが、現状で共通に必要な内容は多くなく、Setup前提の議論になっている。
- ファイルの仮定
  - fから導入される仮定をSetupというStructureにまとめる。
  - Setupには、fやそれから導かれる前順序やSetoid(同値類)が定義されている。
  - fで定義される前順序は、Setup.pre.leとなる。
  - 頂点vからみて、f(v)を親と呼ぶ。Setup.pre.le v (f v)となる。
  - vとf(v)は異なると仮定(s.valid)しても同じ場合を許しても、言明としては同値になる。とりあえず異なると仮定して考えている。 
  - 考える仮定Setupは、主定理の証明のために、このあと、一般化されたり特殊な場合に帰着されたりする。
- ファイルの各内容 
  - 補題(qClass_setup)：function fが与えられると、V上に前順序における頂点の同値類ができる。
  - この同値類に対して、setoidを考えることができる。Setup.setoid.
  - Setupの仮定のもとで、前順序に対するidealを考えている(pre_closuresystem)。idealは、集合族でいうhyperedgeである。
  - fから前順序を定義する方法は、transitive closureを考えるルートと、vとf(v)の関係に両立する集合族から考えるルートの2通りがあって、それらは一致することも示している。le_eq_Rやpre_closuresystem_eq_lem。この定理は主定理の証明にも利用。
  

## 前順序の性質 (functionalTreePreorder.lean)

- このファイル(functionalTreePreorder.lean)は、fから導かれるPreorder的な性質のまとめ。Commonを引き継ぐ内容。ファイル名は、Tree上の構造に前順序を定義するところからきている。
- fから前順序を定義する時に、idealを考えてから前順序を考える方法と2項関係を考えて、そのtransitive closureを考える方法がある。どちらでも同じ前順序が得られる。size_one_preorder_setup_lemma。内容的にはpre_closuresystem_eq_lemの内容と被る。
- 補題：前順序の大小関係と、親の関係で辿れるのは同値。f_and_pre, iteratef_lemma, iteratef_lemma_ref
- 補題：同値類の大きさが2以上のところはpreorderの極大要素である。eqClass_size_ge_two_implies_outside
- 補題：同値な要素の親は同値。f_on_equiv

## 同値類上の半順序の定義 (functionalTreePartialOrder.lean)

- このファイルfunctionalTreePartialOrder.leanはfから導かれる同値類の上の半順序に関するもの。同値類上で定義されているので前順序ではなく、半順序になる。
- 同値類上の半順序とSetup2
  - 考えている仮定は、引き続きSetup。Setupの仮定のもと、頂点の同値類上に半順序が定義できる。半順序関係の定義は、同値類Aから同値類Bに順序の大小があることを、任意の順序idealに対して、同値類Aを含んでいるならば同値類Bを含んでいるということと、定義する。
  - この半順序の枠組みをSetup2としている。仮定としての強さは、Setupと同じ。半順序はfから決定するのでSetupから同値類上の半順序も決まる。Setup2.po.le。
  - この2項関係Setup2.po.leは、半順序の公理を満たす。partialOrder_from_preorder
  - preorderとsetoid上のpartialOrderの関係を色々示す。- fから定義された前順序と同値類上の半順序の関係は pullback_preorder_lemma. pushforward_preorder_lemma
- 極大性
  - setoidの要素の極大性is_MaximalQも定義する。
  - preorderの極大性との関係を示す。isMaximal_iff
- 親関数
  - fの同値類版が、fqという関数。Setup2.fq。
  - fとfqの関係も示す。f_on_equiv_n.
  - fq単独の性質も示す。fqで辿れることと、半順序の関係。fq_lemma。fq_lemma_rev。reach_po_leq

## 同値類上の半順序が作る集合族 (functionalSPO.lean)

- 概要
  - このファイルは、Setup_spoという同値類上の半順序に関する仮定に関する補題を集めたもの。
  - Setup_spoは、Setup2よりも一般化されている仮定。spoは、fや前順序からスタートするのではなく、setoid上の同値類からスタートしている。
  - 前順序を前提にしないSetoid上の半順序を抽象化した仮定がSetup_spo2。これは、SPO2のファイルで出てくる。Setup_spoはSetup2から極大なところ以外は同値類の大きさが1であるというsingleton_if_not_maximalの仮定を外したもの。とりあえず、この仮定はしばらく使わないので、簡単化のために外している。
  - validの仮定があると、極大な同値類の大きさが1にならないが、Setup_spoやSetup_spo2の仮定においては、極大な部分の同値類の大きさは1になりうる。仮定の種類が無駄に増えている気もするので、validの仮定なしで元の言明を書き直した方がいいのかも。
- ファイルの内容
  - 与えられた要素が属する同値類を与える関数classOfを定義している。Setup_spo前提。
  - Setup_spoとreachの関係についても補題を示している。reach_leqとreach_leq_rev。
  - Setup_spoとSetup2の関係なども示す。
  - パラレルな頂点をtraceした集合族もこれにより、前順序を定めることができる。サイズ2以上の同値類から同値な頂点をひとつtraceしても、半順序の親がたかだか1つということも変わらない。

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
- ファイルの内容
  - 補題(eqClass_Maximal)：サイズが2以上の同値類は、半順序の極大要素に対応するところにしか出てこない。setup2_induces_spoで利用。
  - 補題(setup_trace_spo_le)：大小関係があるときは、traceしても大小関係（spo_le）がある。
  - 定義(setup_trace_spo2)：サイズ2以上の同値類からパラレルな頂点をひとつtraceしても、サイズが2以上の同値類が極大なものに限られることも変わらない。つまり、またSetup_spo2になる。

## 同値類上の半順序が作る集合族 (functionalTreeIdeal.lean)

- 順序idealとは、考えている前順序で、下に閉じている集合のことである。順序idealの定義やその性質。
- pre_closuresystemは、前順序から作ったideal。Commonで定義済み。
- pre2_closuresystemは、Setup2のpoを利用して作ったideal。
- 補題(Preorder_eq_PartialOrder)：hyperedgeの集合の全体(pre_closuresystem)は、この半順序の順序ideal(pre2_closuresystem)に一致する。
- spo_closuresystemは、Setup_spoの仮定から作ったideal。
- 補題(Setup_spo_eq_PartialOrder)：spo_closuresystemは、pre2_closuresystemと一致する。

## 順序idealと平均rare (functionalIdealRare.lean)

- 頂点集合上に前順序が与えられると順序idealの全体が決まる。これは集合族のhyperedgeと思って、平均rareになるかが議論できる。
- 平均rareとは、標準化次数和が非正(順序idealの大きさの和*2-順序idealの個数*台集合の大きさ)<=0のことである。
- 補題(spo2_rare): Setup_spo2の仮定のもと、サイズ2以上の同値類の頂点は、rareな頂点になる。
- ここで、Setup_spo2の仮定を利用している。

## 半順序のtrace (functionalTraceIdeal.lean)

- 概要
  - 同値な頂点(パラレルな頂点とも呼ぶ)のひとつをtraceすることにより、同一視していく方向性。
  - 基本的にSetup_spoの仮定の仮定で考えている。
  - 集合族としては、パラレルな頂点を持つ頂点をtraceしていくことにより、パラレルな頂点を持たない集合族を得ることができる。この議論自体はMainで行なっている。ここではその準備。
- ファイルの内容  
  - 定理(trace_ideal_nds ):traceしたものと、集合族が等しければ、標準化次数和ndsも等しい。
  - excessもここで定義。excessは、同値類の大きさがすべて1であるときを0として、それからパラレルな要素があるたびに1ずつ増加していく関数。
  - 補題(trace_excess_decrease):traceすることで、excessはひとつ減る。Setup_spoの仮定でもよいかも。

## 半順序のtrace (functionalTraceIdeal2.lean)

- 概要
  - 半順序の構造Setup_poとの橋渡しの部分。Mainにあるsetup_po_average_rareに必要な補題を証明。
  - 同値類の大きさが全部1であれば、Setup_poとみなせるということを示すのがメイン。
  - trace_ideal_nds_increaseのところで、Setup_spo2の仮定を使っている。
  - spo2_rareを呼んでいて、これがSetup_spo2の仮定を使っている。
  - Setup_spo2の仮定は、同値類の大きさが1であることを仮定しているので、traceした後の集合族は、同値類の大きさが1であることがわかる。
- ファイルの内容
  - 補題(excess_zero): excessは0であれば、同値類の大きさがすべて1。
  - 補題(trace_ideal_nds_increase2)： 集合族に対して、パラレルな要素を持つ要素で、rareな頂点をtraceして平均rareであれば、もともと平均rareである。 
  - この補題は順序とは関係なく、一般に成り立つ。
  - この補題の証明は、すでにParallel.leanのファイルの中で完了している。しかし、それを利用して証明しているわけではない。
  - Setup_poの定義や、半順序に対するidealの定義も。po_closuresystem

## Mainの中の補題 (functionalMain.lean)

- functionalMainの中で大枠の議論をしている。
- setup_average_rareがSetupの仮定を使って書いたメイン定理。
- 今まで証明したことであるPreorder_eq_PartialOrderとSetup_spo_eq_PartialOrderを利用して、setup_spo2_average_rareの仮定のもと、メイン定理は証明される。つまり、Setup前提のaverage rareの定理をSetup_spo2前提のaverage rareの定理に帰着している。setup_spo2_average_rare
- 定理(setup_spo2_average_rare)：同値類上の半順序が与えられていて、同値類の大きさが2以上なのは、極大なものに限る場合は、平均rareになる。
- 補題(trace_ideal_nds_increase2): 集合族に対して、パラレルな要素を持つものが平均rareであることを示すためには、サイズ2以上の同値類をすべて1頂点にまでtraceしたものが平均rareであることを示せば良い。setup_spo2_average_rareの証明でこの言明を利用。
- setup_spo2_average_rareはパラレルな頂点の個数に関する帰納法で示すことができる。サイズがkの同値類があれば、k-1を足すということでbase caseが0にするとよい。

## 半順序の平均rare (functionalPartialTrace.lean)

- ここまでで、サイズ2以上の同値類はないと仮定してよくなったので、同値類のサイズは全部1で、頂点集合ground上の半順序と思うことができる。
- パラレルな頂点がなくなったあとは、グラフ論の森(forest)で各連結成分に根が指定されているものと思うことができる。根から遠い頂点が下となる。
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
-
- functionalDirectProductは、それぞれの側に関して、Setup_poを定義することが目標。
  - comp_poとexcl_po
- 以下、functionaDirectProduct2.leanの内容。
- directProduct_comp_excel_ground_cとdirectProduct_comp_excel_ground_eで、台集合が真に小さくなっていることを示している。
- directProduct_ndsが目標。集合族がqを含む部分と含まない部分の直積でかけるときに、normalized_degree_sumが両方とも非正であれば、直積も非正になることを示すことができた。
  - directProduct_nds。

## 半順序の平均rare (functionalMain.leanの一部)

- Mainのファイルで、setup_po_average_rare_card_oneとして帰納法で証明する。
- ベースケース（|V| = 1、excess = 0）を分離 
- 強い再帰 / measure 降下で一般ケースへ。
- trace と 直積分解 を交互に用いて ground を strictに減らし、
- Normalized Degree Sum が単調に減らない（≦0）ことを保証。
- 最終的に関数 f が導く前順序由来の集合族が average rare であることを示す。

## 全体的なリファクタリング予定のまとめ

- 主定理からvalidの条件をなくす。
- functionalCommon.leanは、commonというより、主定理のための定義だがどうするか。名前を変える？
- Setup2を無くして、Setupに関数を定義する。
- 全体的にSetupなどの仮定に依存する部分を減らして、部品を共通化したい。
- ファイル名の統一が取れていない。Mainのファイルの定理のどの定理から引用されるかでファイルをわけるといいかも。
