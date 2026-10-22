(* Shared implementation of Application 4. Load with Get, then App4Solve["transpose"|"inverse", n, d].
   Coefficients use unnormalized channel Choi matrices: C0=1 and Tr[C]=d^(n+1).
   Exact matrix-unit data remain authoritative; only the SDP is numerical. *)
ClearAll[FName, irrepDims, BT, SortB, FlipPair, WalledBrauerGenerators,
 WalledBrauerBasis, ContractDiag, ContractOne, Contract, FullContract,
 ContractOne2, Contract2, FullContract2, MultiplyPair2, MultiplyPair,
 Str, x, prodRule, mulTensor, contractTensor, contractIdTensor,
 mulTensorMatrix, MulContractTensor, FullContractVec, MultiplyVecs, psd,
 Contract2Vec, Osys, Psys, Isys, Fsys, Choi, TrChoi, ChoiTensorId,
 blocksLoad, blocksLoadN, vec2ToBlocks, vec2ToBlocksN, vec2ToBlocksBetter,
 vec2ToBlocksBetterN, App4Solve, App4Table2Value];

app4DataDirectory = DirectoryName[$InputFileName];
FName[name_, p_, q_, d_] :=
  FileNameJoin[{app4DataDirectory, name}] <> "_" <> ToString[p] <> "_" <>
   ToString[q] <> "_" <> ToString[d];
irrepDims[p_, q_, d_] :=
  irrepDims[p, q, d] =
   Import[FName["idempotents/metadata", p, q, d] <> ".m"][[1]];

(* Transpose a Brauer diagram *)
BT[\[Sigma]_] :=
  SortB[B[Sequence @@ (FlipPair[#, 0] & /@ (\[Sigma] /. B -> List))]];
(* Sort the diagram description to make it canonical *)
SortB[\[Sigma]_] := Sort@Map[Sort, \[Sigma], 1];
(*Given the line defined by a pair of vertices, \
flip the vertices which are located after the wall at level p*)
FlipPair[pair_, p_] := Sort@(If[Abs[#] > p, -#, #] & /@ pair);
(*Generate Walled Brauer Algebra generators*)
WalledBrauerGenerators[p_, q_] :=
  WalledBrauerGenerators[p, q] =
   B[Sequence @@ #] & /@
    Map[FlipPair[#, p] &,
     FoldList[ReplacePart[#1, #2 -> {-#2, #1[[#2]]}] &, #,
         Range[p + q]][[-1]] & /@
      Table[Range[i - 1]~Join~{i + 1, i}~Join~Range[i + 2, p + q], {i,
         1, p + q - 1}], {2}];
(*Generate Walled Brauer Algebra basis*)
WalledBrauerBasis[p_, q_] :=
  WalledBrauerBasis[p, q] = (SortB[B[Sequence @@ #]]) & /@
    Map[FlipPair[#, p] &,
     FoldList[ReplacePart[#1, #2 -> {-#2, #1[[#2]]}] &, #,
         Range[p + q]][[-1]] & /@ Permutations[Range[p + q]], {2}];

(* Contract a Brauer diagram at one fixed position l *)
ContractDiag[diag__, {l_, d_}] := Module[{new, data},
   data = diag /. B -> List;
   new =
    Sort@Flatten@
      Table[If[data[[i]] \[Intersection] {-l, l} != {},
        Complement[data[[i]], {-l, l}], {}], {i, 1, Length@data}];
   If[new == {},
    d SortB[B[
       Sequence @@
        Sort@Table[
          If[data[[i]] \[Intersection] {-l, l} != {}, Nothing,
           data[[i]]], {i, 1, Length@data}]]],
    SortB[B[Sequence @@
       Sort@(Table[
           If[data[[i]] \[Intersection] {-l, l} != {}, Nothing,
            data[[i]]], {i, 1, Length@data}]~Join~{new})]]]
   ];
(* Contract a lin. comb. of Brauer diagrams x at one fixed position l \
*)
ContractOne[x_, {l_, d_}] :=
  x /. B[lst__] :> ContractDiag[{lst}, {l, d}];
(* Contract a lin. comb. of Brauer diagrams x at fixed positions lst *)
Contract[x_, lst_List, d_] :=
  Fold[ContractOne, x, {lst, ConstantArray[d, Length@lst]}\[Transpose]];
(* Compute the full trace of a lin. comb. of Brauer diagrams x *)
FullContract[x_, p_, q_, d_] :=
  Contract[x, Table[i, {i, p + q}], d] /. B[] -> 1;
(* Two registers, each with p+q sites. Explicit dimensions avoid global-state errors. *)
ContractOne2[x_, {l_, d_}, p_, q_] :=
 If[l > p + q,
  x /. TensorProduct[B[left___], B[right___]] :>
    TensorProduct[B[left], ContractDiag[{right}, {l - p - q, d}]],
  x /. TensorProduct[B[left___], B[right___]] :>
    TensorProduct[ContractDiag[{left}, {l, d}], B[right]]];
ContractOne2[x_, ld_] := ContractOne2[x, ld, p, q];
Contract2[x_, lst_List, d_, p_, q_] :=
 Fold[ContractOne2[#1, #2, p, q] &, x,
   Transpose[{lst, ConstantArray[d, Length[lst]]}]] /. B[] -> 1;
Contract2[x_, lst_List, d_] := Contract2[x, lst, d, p, q];
FullContract2[x_, p_, q_, d_] :=
 FullContract[Contract2[x, Range[p + q], d, p, q], p, q, d];


(* Multiply two Brauer algebra diagrams *)
MultiplyPair2[\[Sigma]1_, \[Sigma]2_, d_] :=
  Module[{lst, i, new, pos, \[Sigma]1n, \[Sigma]2n},
   \[Sigma]1n =
    Map[If[# < 0, Subscript[b, -#], Subscript[a, #]] &,
     List @@ \[Sigma]1, {2}];
   \[Sigma]2n =
    Map[If[# < 0, Subscript[b, -#], Subscript[a, #]] &,
     List @@ \[Sigma]2, {2}];
   (* Denote the nodes in the middle layer by x *)
   lst = Join[\[Sigma]1n /. b -> x, \[Sigma]2n /. a -> x];
   (* Treat each node Subscript[x, i] in the intermediate level *)
   Do[
    (* Find all edges containing Subscript[x, i] *)
    new = lst[[pos = Position[lst, Subscript[x, i], {2}][[All, 1]]]];
    (* Update the list by removing these edges and adding a new one *)
    lst =
     Append[Delete[lst, List /@ pos],
      DeleteCases[Join @@ new, Subscript[x, i]]];
    , {i, 1, Length[\[Sigma]1]}
    ];
   (* Output the new Brauer diagram and the normalization factor from t\
he number of loops *)
   {B @@
     SortB@Map[If[TrueQ[First[#] == b], -Part[#, 2], Part[#, 2]] &,
       DeleteCases[lst, {}], {2}], d^Count[lst, {}]}
   ];
(* Multiply two Brauer algebra diagrams *)
MultiplyPair[\[Sigma]1_, \[Sigma]2_, d_] :=
  Times @@ MultiplyPair2[\[Sigma]1, \[Sigma]2, d];

(* Convert integer to a string and pad with 0s *)
Str[i_, max_] :=
  StringJoin @@ (ToString /@ IntegerDigits[i, 10, IntegerLength@max]);
(* Shorter variable names that also account for symmetry *)
x[\[Lambda]_, \[Mu]_, i_, j_, k_, l_, dB_] :=
  Symbol["x" <> Str[\[Lambda], Length@dB] <> Str[\[Mu], Length@dB] <>
    StringJoin @@
     Sort[{Str[i, dB[[\[Lambda]]]] <> Str[k, dB[[\[Mu]]]],
       Str[j, dB[[\[Lambda]]]] <> Str[l, dB[[\[Mu]]]]}]];

(* Diagram multiplication tensor *)
prodRule[p_, q_, d_, i_, j_] :=
  Block[{basis = WalledBrauerBasis[p, q], prod},
   prod = MultiplyPair2[basis[[i]], basis[[j]], d]; {i, j,
     Position[basis, prod[[1]]][[1, 1]]} -> prod[[2]]];
mulTensor[p_, q_, d_] :=
  mulTensor[p, q, d] =
   SparseArray[
    Flatten@Table[
      prodRule[p, q, d, i, j], {i, 1, (p + q)!}, {j,
       1, (p + q)!}], {(p + q)!, (p + q)!, (p + q)!}];

(* Diagram contraction tensor *)
contractTensor[p_, q_, d_] :=
  contractTensor[p, q, d] =
   Table[FullContract[WalledBrauerBasis[p, q][[i]], p, q, d], {i,
     1, (p + q)!}];
contractTensor[p_, q_, d_, lst_] :=
  contractTensor[p, q, d, lst] =
   Table[(Contract[WalledBrauerBasis[p, q][[i]], lst,
         d] /. {(B[y__] :>
           B[Sequence @@ ({y} /.
               Flatten[{#[[1]] -> #[[
                    2]], -#[[1]] -> -#[[2]]} & /@ ({Complement[
                    Range[p + q], lst], Range[p + q - Length[lst]]}\[Transpose])])])})
      /. {B[] :> 1,
       B[arg__] :>
        SparseArray[{Position[
             WalledBrauerBasis[p - Count[lst, x_ /; x <= p],
              q - Count[lst, x_ /; x > p]], B[arg], {1}][[1, 1]]} ->
          1, (p + q - Length[lst])!]}, {i, 1, (p + q)!}]\[Transpose];

(* Diagram contraction and adding Id tensor *)
contractIdTensor[p_, q_, d_, lstContract_, lstId_] :=
 contractIdTensor[p, q, d, lstContract, lstId] =
  Table[(Contract[WalledBrauerBasis[p, q][[i]], lstContract,
        d] /. (B[y___] :>
         SortB@B[Sequence @@ ({y,
               Sequence @@ ({-#, #} & /@ lstId)} /.
              Flatten[{#[[1]] -> #[[
                    2]], -#[[1]] -> -#[[2]]} & /@ ({Complement[
                    Range[p + q], Complement[lstContract, lstId]],
                   Range[p + q - Length[lstContract] +
                    Length[lstId]]}\[Transpose])])])) /.
     {B[] :> 1,
      B[arg__] :>
       SparseArray[{Position[
            WalledBrauerBasis[
             p - Count[Complement[lstContract, lstId], x_ /; x <= p],
             q - Count[Complement[lstContract, lstId], x_ /; x > p]],
            B[arg], {1}][[1, 1]]} ->
         1, (p + q - Length[lstContract] + Length[lstId])!]}
    , {i, 1, (p + q)!}]\[Transpose]

(* Auxiliary tensors *)
mulTensorMatrix[p_, q_, d_] :=
  mulTensorMatrix[p, q, d] = Flatten[mulTensor[p, q, d], {{1, 2}, {3}}];
MulContractTensor[p_, q_, d_] :=
 MulContractTensor[p, q, d] =
  ArrayReshape[
   mulTensorMatrix[p, q, d] .
    contractTensor[p, q, d], {(p + q)!, (p + q)!}]

(* Operations on 1vecs *)
FullContractVec[vec_, p_, q_,
  d_] := (contractTensor[p, q, d] . {vec}\[Transpose])[[1]]
MultiplyVecs[vec1_, vec2_, p_, q_, d_] :=
 Flatten[KroneckerProduct[vec1, vec2]] . mulTensorMatrix[p, q, d]
MultiplyVecs[vec1_, vec2_, vec3_, p_, q_, d_] :=
 MultiplyVecs[vec1, MultiplyVecs[vec2, vec3, p, q, d], p, q, d]

(*Define psd constraints and make them symmetric*)
psd[\[Lambda]_, \[Mu]_, p_, q_, d_] :=
  psd[\[Lambda], \[Mu], p, q, d] =
   Flatten[Table[
     x[\[Lambda], \[Mu], i, j, k, l, irrepDims[p, q, d]], {i, 1,
      irrepDims[p, q, d][[\[Lambda]]]}, {k, 1,
      irrepDims[p, q, d][[\[Mu]]]}, {j, 1,
      irrepDims[p, q, d][[\[Lambda]]]}, {l, 1,
      irrepDims[p, q, d][[\[Mu]]]}], {{1, 2}, {3, 4}}];

(*Contract vec, \
which has the form \[Sum]KroneckerProduct[*\
,*] on given list of indices *)
Contract2Vec[vec_, p_, q_, d_, lst_] :=
 contractTensor[p, q, d, Select[lst, # <= (p + q) &]] . vec .
  contractTensor[p, q, d, Select[lst, # > (p + q) &] - (p + q)]\[Transpose]
Contract2Vec[vec_, p_, q_, d_] :=
 Contract2Vec[vec, p, q, d, Range[2 (p + q)]]

(* Define order on registers *)
Osys[p_, q_] := Range[1, p + q - 1];
Psys[p_, q_] := {p + q};
Isys[p_, q_] := Range[p + q + 1, 2 (p + q) - 1];
Fsys[p_, q_] := {2 (p + q)};

(* Realise linear constraints *)
Choi[ansatz_, i_, p_, q_, d_] :=
 If[i < p + q,
  Expand[If[i == 0, Contract2Vec[ansatz, p, q, d],
     Contract2Vec[ansatz, p, q, d,
      Osys[p, q][[i ;; p + q - 1]]~Join~
       Isys[p, q][[i + 1 ;; p + q - 1]]~Join~Fsys[p, q]]]/d^(
    p + q - i)], ansatz]

TrChoi[ansatz_, i_, p_, q_, d_] :=
 If[i == 0, Print["Error: i should be >0"],
  Expand[Contract2Vec[ansatz, p, q, d,
     Osys[p, q][[i ;; p + q - 1]]~Join~Isys[p, q][[i ;; p + q - 1]]~
      Join~Fsys[p, q]]/d^(p + q - i)]]

ChoiTensorId[ansatz_, i_, p_, q_, d_] := Expand[If[i >= 1,
    contractIdTensor[p, q, d, Osys[p, q][[i ;; p + q - 1]],
      Osys[p, q][[i ;; i]]] . ansatz .
     contractTensor[p, q,
       d, (Isys[p, q][[i + 1 ;; p + q - 1]]~Join~Fsys[p, q]) - (p + q)]\[Transpose],
    contractIdTensor[p, q, d, Osys[p, q]~Join~Psys[p, q],
      Psys[p, q]] . ansatz .
     contractTensor[p, q,
       d, (Isys[p, q][[i + 1 ;; p + q - 1]]~Join~Fsys[p, q]) - (p + q)]\[Transpose]
    ]/d^(p + q - i)]

(* Load blocks *)
ClearAll[blocksLoad, blocksLoadN]
blocksLoad[p_, q_, d_] :=
 blocksLoad[p, q, d] = Import[FName["blocks/blocks", p, q, d] <> ".m"]
blocksLoadN[p_, q_, d_, prec_] :=
 blocksLoadN[p, q, d, prec] = N[blocksLoad[p, q, d], prec]

(* Map 2vec to selected blocks *)
vec2ToBlocks[vec_, \[Lambda]_, \[Mu]_, p\[Lambda]_, q\[Lambda]_,
  p\[Mu]_, q\[Mu]_, d_] :=
 Sum[vec[[i, j]] KroneckerProduct[
    blocksLoad[p\[Lambda], q\[Lambda], d][[i, \[Lambda]]],
    blocksLoad[p\[Mu], q\[Mu], d][[j, \[Mu]]]], {i,
   1, (p\[Lambda] + q\[Lambda])!}, {j, 1, (p\[Mu] + q\[Mu])!}]
vec2ToBlocksN[vec_, \[Lambda]_, \[Mu]_, p\[Lambda]_, q\[Lambda]_,
  p\[Mu]_, q\[Mu]_, d_, prec_] :=
 Sum[vec[[i, j]] KroneckerProduct[
    blocksLoadN[p\[Lambda], q\[Lambda], d, prec][[i, \[Lambda]]],
    blocksLoadN[p\[Mu], q\[Mu], d, prec][[j, \[Mu]]]], {i,
   1, (p\[Lambda] + q\[Lambda])!}, {j, 1, (p\[Mu] + q\[Mu])!}]

(* Map 2vec to selected blocks *)
vec2ToBlocksBetter[vec_, \[Lambda]_, \[Mu]_, p\[Lambda]_, q\[Lambda]_,
   p\[Mu]_, q\[Mu]_, d_] :=
 Flatten[vec] .
  Flatten[Outer[KroneckerProduct,
    blocksLoad[p\[Lambda], q\[Lambda], d][[All, \[Lambda]]],
    blocksLoad[p\[Mu], q\[Mu], d][[All, \[Mu]]], 1], {{1, 2}, {3}, {4}}]
vec2ToBlocksBetterN[vec_, \[Lambda]_, \[Mu]_, p\[Lambda]_,
  q\[Lambda]_, p\[Mu]_, q\[Mu]_, d_, prec_] :=
 Flatten[vec] .
  Flatten[Outer[KroneckerProduct,
    blocksLoadN[p\[Lambda], q\[Lambda], d, prec][[All, \[Lambda]]],
    blocksLoadN[p\[Mu], q\[Mu], d, prec][[All, \[Mu]]],
    1], {{1, 2}, {3}, {4}}]

(* Table 2 entries are printed to six decimals; Missing means outside that table. *)
App4Table2Value[task_, n_, d_] := Which[
 !MemberQ[{"transpose", "inverse"}, task] || !MemberQ[Range[4], n], Missing["NotTabulated"],
 d == 2, {1/2, 3/4, (2 + Sqrt[3])/4, 1}[[n]],
 d == 3 && task == "inverse", (n + 1)/9,
 d == 3 && task == "transpose", {2/9, 11/27, 0.626597, 0.799250}[[n]],
 True, Missing["NotTabulated"]];

Options[App4Solve] = {"VerifyExactAnsatz" -> False};
App4Solve::case = "Use task \"transpose\" or \"inverse\", integer n >= 1 and integer d >= 2.";
App4Solve::data = "Required matrix-unit data are missing: `1`. Generate the corresponding case first.";
App4Solve::solve = "SemidefiniteOptimization did not return numerical rules for every variable.";
App4Solve[task_, n_, dimension_, OptionsPattern[]] := Module[
 {p, q, d = dimension, dims, units, unitsN, dimU, ansatzNumeric, exactAnsatz,
  omega, metric, objective, rawConstraints, constraints, psdBlocks, psdConstraints,
  vars, solutionRules, solution, fidelity, residual, minimumEigenvalue, exactError,
  expected, dataFile, start = AbsoluteTime[]},
 If[!MemberQ[{"transpose", "inverse"}, task] || !IntegerQ[n] || n < 1 ||
    !IntegerQ[d] || d < 2, Message[App4Solve::case]; Return[$Failed]];
 {p, q} = If[task == "transpose", {n, 1}, {n + 1, 0}];
 dataFile = FName["idempotents/elementary", p, q, d] <> ".m";
 If[!FileExistsQ[dataFile], Message[App4Solve::data, dataFile]; Return[$Failed]];
 dims = irrepDims[p, q, d];
 units = Import[dataFile]; unitsN = N[units, 50];
 dimU = Table[FullContractVec[units[[lambda, 1, 1]], p, q, d],
   {lambda, Length[dims]}];
 (* Same matrix-unit expansion as (177), evaluated numerically before expansion. *)
 ansatzNumeric = Plus @@ Flatten[Table[
   x[lambda, mu, i, j, k, l, dims] KroneckerProduct[
     unitsN[[lambda, i, j]], unitsN[[mu, k, l]]],
   {lambda, Length[dims]}, {mu, Length[dims]},
   {i, dims[[lambda]]}, {j, dims[[lambda]]},
   {k, dims[[mu]]}, {l, dims[[mu]]}], 5];
 omega = Sum[KroneckerProduct[unitsN[[lambda, i, j]], unitsN[[lambda, i, j]]]/
    (d^2 dimU[[lambda]]), {lambda, Length[dims]},
    {i, dims[[lambda]]}, {j, dims[[lambda]]}];
 metric = Transpose[MulContractTensor[p, q, d]] . Transpose[omega] .
   MulContractTensor[p, q, d];
 objective = Chop[Total[Expand[Flatten[Transpose[metric]] Flatten[ansatzNumeric]]]];
 rawConstraints = Table[Chop[TrChoi[ansatzNumeric, i, p, q, d] -
   ChoiTensorId[ansatzNumeric, i - 1, p, q, d]], {i, p + q}];
 constraints = Chop[Flatten[Join[
   {Choi[ansatzNumeric, 0, p, q, d] - 1}, rawConstraints[[1 ;; 2]],
   Table[Table[Expand[vec2ToBlocksBetterN[rawConstraints[[i]], lambda, mu,
     i - q, q, i - 1, 0, d, 50]],
     {lambda, Length[irrepDims[i - q, q, d]]},
     {mu, Length[irrepDims[i - 1, 0, d]]}], {i, 3, p + q}]]]];
 psdBlocks = Flatten[Table[psd[lambda, mu, p, q, d],
   {lambda, Length[dims]}, {mu, Length[dims]}], 1];
 psdConstraints = (VectorGreaterEqual[{#, 0}, {"SemidefiniteCone", Length[#]}] &) /@ psdBlocks;
 vars = Variables[psdBlocks];
 (* Optional independent expansion check. It is intentionally absent from the normal SDP path.
    Compare every coefficient, not only the value at the optimized solution. *)
 exactError = Missing["NotRequested"];
 If[TrueQ[OptionValue["VerifyExactAnsatz"]],
  exactAnsatz = Expand[Sum[x[lambda, mu, i, j, k, l, dims]
    KroneckerProduct[units[[lambda, i, j]], units[[mu, k, l]]],
    {lambda, Length[dims]}, {mu, Length[dims]},
    {i, dims[[lambda]]}, {j, dims[[lambda]]},
    {k, dims[[mu]]}, {l, dims[[mu]]}]];
  exactError = Max[Abs[Flatten[Normal /@
    CoefficientArrays[Flatten[exactAnsatz - ansatzNumeric], vars]]]]];
 solutionRules = SemidefiniteOptimization[-objective,
   Join[psdConstraints, (# == 0 &) /@ constraints], vars];
 If[!ListQ[solutionRules] || !VectorQ[vars /. solutionRules, NumericQ],
  Message[App4Solve::solve]; Return[$Failed]];
 solution = Dispatch[solutionRules];
 fidelity = N[objective /. solution];
 residual = Max[Abs[N[constraints /. solution]]];
 minimumEigenvalue = Min[Flatten[Eigenvalues[N[# /. solution]] & /@ psdBlocks]];
 expected = App4Table2Value[task, n, d];
 <|"Task" -> task, "Calls" -> n, "Dimension" -> d, "Wall" -> {p, q},
   "Fidelity" -> fidelity, "Table2Value" -> N[expected],
   "Table2Agreement" -> If[MissingQ[expected], expected, Abs[fidelity - N[expected]] < 5 10^-7],
   "EqualityResidual" -> residual, "MinimumBlockEigenvalue" -> minimumEigenvalue,
   "FeasibleWithin1e-7" -> (residual < 10^-7 && minimumEigenvalue > -10^-7),
   "VariableCount" -> Length[vars], "ConstraintCount" -> Length[constraints],
   "ExactAnsatzCoefficientError" -> exactError,
   "ElapsedSeconds" -> N[AbsoluteTime[] - start]|>
];
