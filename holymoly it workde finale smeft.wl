(* ::Package:: *)

(* ::Title:: *)
(*SMEFT :)*)


(* ::Chapter:: *)
(*Lagrangian with MINIBAR*)


Quit[]


(* ::Text:: *)
(*Laptop*)


AppendTo[$Path, "C:\\Users\\rugje\\Desktop\\Projekt\\BTR Thesis\\minimalMINIBAR\\minimalMINIBAR"];
Needs["MINIBAR`"]


AppendTo[$Path, "/home/joan/Work/minibar/ChPTLagrangian/MMA/MINIBAR/"];
Needs["MINIBAR`"]


AppendTo[$Path, "C://Users//dj875//OneDrive//Desktop//BTR//minimalMINIBAR"];
Needs["MINIBAR`"]


(* ::Subsection::Closed:: *)
(*Configuration SMEFT     <---Run this*)


(* ::Subsubsection:: *)
(*Helpers to debug [SMEFT]*)


(* ::Subsubsubsection:: *)
(*New function definitions*)


(* ::Text:: *)
(*In MINIBAR.m there is a version of readableNotation. Here superseded *)


Clear[readableNotation]
readableNotation[expr_]:=expr/.

DD[field_,nder_?(#>0&)][a___,lor[ind___],b___]:>(
indMod = {ind}//readableIndex//Sequence@@#&;
nInd=Length[{ind}]-nder;
Which[
nInd==0 &&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}] . (cal[field]),
nInd!= 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}] . (Subscript[cal[field], lor[Sequence@@List[indMod][[nder+1;;nder+nInd]]]])])/.

DD[field_,nder_][ind___]:>(
indMod = {ind}//readableIndex//Sequence@@#&;
nInd=Length[{ind}]-nder;
Which[
nInd==0 &&nder==0,cal[field] ,
nInd==0 &&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}] . (cal[field]),
nInd!= 0&&nder==0, Subscript[cal[field], Sequence@@List[indMod]],
nInd!= 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}] . (Subscript[cal[field], Sequence@@List[indMod][[nder+1;;nder+nInd]]])])/.

GA[g_,___][ind___]:>(
indMod = {ind}//readableIndex//Sequence@@#&;
nInd=Length[{ind}];
Which[
nInd==0,cal[g] ,
nInd!=0, Subscript[cal[g], Sequence@@List[indMod]]])

(*DD[psiL,3][lor[j1,j2,j1]]
%//readableNotation*)


(* ::Text:: *)
(*Completely new function: contractIndices. This is only for visualising the terms without the indices (to define seeBilinears)*)
(**)
(*However, know that the MINIBAR function //see does not use this new function contractIndices. And that is why //checkRules will crash with the new notation.*)
(**)


ClearAll[contractIndicesOLD];
contractIndicesOLD//allowLists

contractIndicesOLD::arity =
  "Each factor may carry at most one outer `1`[...] block, and that block \
may contain at most two indices. Offending factor: `2`.";

contractIndicesOLD::bad =
  "The `1`-index factors do not form disjoint non-branching open chains or closed cycles.";

contractIndicesOLD[type_][term_] := Module[
  {
    factors, parse, data, scalars, active, singles, mats,
    matsByStart, matsByEnd, singlesByIndex,
    firstIdxs, secondIdxs, unused, use,
    openStarts, components = {},
    start, seq, current, startIndex, nextMat, nextSingle
  },

  factors = If[Head[term] === Times, List @@ term, {term}];

  parse[expr_] := Replace[
    expr,
    {
      HoldPattern[h_[args___]] :> Module[
        {outer = {args}, blocks, restArgs},
        blocks = Cases[outer, HoldPattern[type[inds___]] :> {inds}, {1}];

        If[
          Length[blocks] > 1 || (blocks =!= {} && Length[First[blocks]] > 2),
          Message[contractIndices::arity, HoldForm[type], HoldForm[expr]];
          Throw[$Failed]
        ];

        restArgs = DeleteCases[outer, HoldPattern[type[___]], {1}];

        <|
          "full" -> expr,
          "bare" -> h[Sequence @@ restArgs],
          "idxs" -> If[blocks === {}, {}, First[blocks]]
        |>
      ],

      other_ :> <|"full" -> other, "bare" -> other, "idxs" -> {}|>
    }
  ];

  data = Catch @ MapIndexed[Append[parse[#1], "id" -> First[#2]] &, factors];
  If[data === $Failed, Return[$Failed]];

  scalars = Lookup[Select[data, #idxs === {} &], "full", {}];
  active  = Select[data, 1 <= Length[#idxs] <= 2 &];
  singles = Select[active, Length[#idxs] == 1 &];
  mats    = Select[active, Length[#idxs] == 2 &];

  matsByStart    = GroupBy[mats, First @ #idxs &];
  matsByEnd      = GroupBy[mats, Last  @ #idxs &];
  singlesByIndex = GroupBy[singles, First @ #idxs &];

  If[
    AnyTrue[Values[matsByStart], Length[#] > 1 &] ||
    AnyTrue[Values[matsByEnd],   Length[#] > 1 &] ||
    AnyTrue[Values[singlesByIndex], Length[#] > 1 &],
    Message[contractIndices::bad, HoldForm[type]];
    Return[$Failed]
  ];

  unused = AssociationThread[Lookup[active, "id"], ConstantArray[True, Length[active]]];
  use[id_] := KeyDropFrom[unused, id];

  firstIdxs  = First /@ Lookup[mats, "idxs"];
  secondIdxs = Last  /@ Lookup[mats, "idxs"];

  (* Open chains: start from 1-index factors whose index is not a matrix "end" *)
  openStarts = Select[singles, FreeQ[secondIdxs, First[#idxs]] &];

  Do[
    If[KeyExistsQ[unused, start["id"]],
      seq = {start["bare"]};
      current = First[start["idxs"]];
      use[start["id"]];

      While[True,
        nextMat = Select[Lookup[matsByStart, current, {}], KeyExistsQ[unused, #id] &];

        If[nextMat === {}, Break[]];
        If[Length[nextMat] =!= 1,
          Message[contractIndices::bad, HoldForm[type]];
          Return[$Failed]
        ];

        nextMat = First[nextMat];
        AppendTo[seq, nextMat["bare"]];
        use[nextMat["id"]];
        current = Last[nextMat["idxs"]];

        nextSingle = Select[Lookup[singlesByIndex, current, {}], KeyExistsQ[unused, #id] &];
        If[nextSingle =!= {},
          If[Length[nextSingle] =!= 1,
            Message[contractIndices::bad, HoldForm[type]];
            Return[$Failed]
          ];
          AppendTo[seq, First[nextSingle]["bare"]];
          use[First[nextSingle]["id"]];
          Break[]
        ];
      ];

      AppendTo[components, Dot @@ seq]
    ],
    {start, openStarts}
  ];

  (* Closed cycles: whatever 2-index factors are left *)
  Do[
    If[KeyExistsQ[unused, start["id"]],
      seq = {start["bare"]};
      startIndex = First[start["idxs"]];
      current = Last[start["idxs"]];
      use[start["id"]];

      While[current =!= startIndex,
        nextMat = Select[Lookup[matsByStart, current, {}], KeyExistsQ[unused, #id] &];

        If[Length[nextMat] =!= 1,
          Message[contractIndices::bad, HoldForm[type]];
          Return[$Failed]
        ];

        nextMat = First[nextMat];
        AppendTo[seq, nextMat["bare"]];
        use[nextMat["id"]];
        current = Last[nextMat["idxs"]];
      ];

      AppendTo[components, TR @@ seq]
    ],
    {start, mats}
  ];

  If[unused =!= <||>,
    Message[contractIndices::bad, HoldForm[type]];
    Return[$Failed]
  ];

  Times @@ Join[scalars, components] /. Times[] -> 1
];


ClearAll[contractIndices];
contractIndices//allowLists

contractIndices::arity =
  "Each factor may carry at most one outer `1`[...] block, and that block \
may contain at most two indices. Offending factor: `2`.";

contractIndices::bad =
  "The `1`-index factors do not form disjoint non-branching open chains or closed cycles.";

contractIndices[type_][term_] := Module[
  {
    factors, parse, data, scalars, active, singles, mats,
    matsByStart, matsByEnd, singlesByIndex,
    allIndices, localPattern,
    unused, use, openStarts, directPairs, components = {},
    start, seq, current, startIndex, nextMat, nextSingle, grp
  },

  factors = timesToList[term];
  
  parse[expr_] := Replace[
    expr,
    {
      HoldPattern[h_[args___]] :> Module[
        {outer = {args}, blocks, restArgs},
        blocks = Cases[outer, HoldPattern[type[inds___]] :> {inds}, {1}];

        If[
          Length[blocks] > 1 || (blocks =!= {} && Length[First[blocks]] > 2),
          Message[contractIndices::arity, HoldForm[type], HoldForm[expr]];
          Throw[$Failed]
        ];

        restArgs = DeleteCases[outer, HoldPattern[type[___]], {1}];

        <|
          "full" -> expr,
          "bare" -> h[Sequence @@ restArgs],
          "idxs" -> If[blocks === {}, {}, First[blocks]]
        |>
      ],

      other_ :> <|"full" -> other, "bare" -> other, "idxs" -> {}|>
    }
  ];

  data = Catch @ MapIndexed[Append[parse[#1], "id" -> First[#2]] &, factors];
  If[data === $Failed, Return[$Failed]];

  scalars = Lookup[Select[data, #idxs === {} &], "full", {}];
  active  = Select[data, 1 <= Length[#idxs] <= 2 &];
  singles = Select[active, Length[#idxs] == 1 &];
  mats    = Select[active, Length[#idxs] == 2 &];

  If[active === {}, Return[Times @@ scalars /. Times[] -> 1]];

  matsByStart    = GroupBy[mats, First @ #idxs &];
  matsByEnd      = GroupBy[mats, Last  @ #idxs &];
  singlesByIndex = GroupBy[singles, First @ #idxs &];

  allIndices = Union[Keys[matsByStart], Keys[matsByEnd], Keys[singlesByIndex]];

  localPattern[idx_] := {
    Length @ Lookup[singlesByIndex, idx, {}],
    Length @ Lookup[matsByStart, idx, {}],
    Length @ Lookup[matsByEnd, idx, {}]
  };

  If[
    AnyTrue[Values[matsByStart], Length[#] > 1 &] ||
    AnyTrue[Values[matsByEnd],   Length[#] > 1 &] ||
    AnyTrue[
      allIndices,
      ! MemberQ[{{2,0,0}, {1,1,0}, {1,0,1}, {0,1,1}}, localPattern[#]] &
    ],
    Message[contractIndices::bad, HoldForm[type]];
    Return[$Failed]
  ];

  unused = AssociationThread[Lookup[active, "id"], ConstantArray[True, Length[active]]];
  use[id_] := KeyDropFrom[unused, id];

  (* Direct 1-index contractions: a[i] b[i] -> Dot[a,b] *)
  directPairs = Select[allIndices, localPattern[#] === {2,0,0} &];

  Do[
    grp = Lookup[singlesByIndex, idx, {}];
    If[AllTrue[Lookup[grp, "id"], KeyExistsQ[unused, #] &],
      AppendTo[components, Dot @@ Lookup[grp, "bare"]];
      Scan[use, Lookup[grp, "id"]]
    ],
    {idx, directPairs}
  ];

  (* Open chains: start from 1-index factors with pattern {1,1,0} *)
  openStarts = Select[
    singles,
    localPattern[First[#idxs]] === {1,1,0} &
  ];

  Do[
    If[KeyExistsQ[unused, start["id"]],
      seq = {start["bare"]};
      current = First[start["idxs"]];
      use[start["id"]];

      While[True,
        nextSingle = Select[Lookup[singlesByIndex, current, {}], KeyExistsQ[unused, #id] &];
        If[nextSingle =!= {},
          If[Length[nextSingle] =!= 1,
            Message[contractIndices::bad, HoldForm[type]];
            Return[$Failed]
          ];
          AppendTo[seq, First[nextSingle]["bare"]];
          use[First[nextSingle]["id"]];
          Break[]
        ];

        nextMat = Select[Lookup[matsByStart, current, {}], KeyExistsQ[unused, #id] &];
        If[Length[nextMat] =!= 1,
          Message[contractIndices::bad, HoldForm[type]];
          Return[$Failed]
        ];

        nextMat = First[nextMat];
        AppendTo[seq, nextMat["bare"]];
        use[nextMat["id"]];
        current = Last[nextMat["idxs"]];
      ];

      AppendTo[components, Dot @@ seq]
    ],
    {start, openStarts}
  ];

  (* Closed cycles: remaining 2-index factors *)
  Do[
    If[KeyExistsQ[unused, start["id"]],
      seq = {start["bare"]};
      startIndex = First[start["idxs"]];
      current = Last[start["idxs"]];
      use[start["id"]];

      While[current =!= startIndex,
        nextMat = Select[Lookup[matsByStart, current, {}], KeyExistsQ[unused, #id] &];

        If[Length[nextMat] =!= 1,
          Message[contractIndices::bad, HoldForm[type]];
          Return[$Failed]
        ];

        nextMat = First[nextMat];
        AppendTo[seq, nextMat["bare"]];
        use[nextMat["id"]];
        current = Last[nextMat["idxs"]];
      ];

      AppendTo[components, TR @@ seq]
    ],
    {start, mats}
  ];

  If[unused =!= <||>,
    Message[contractIndices::bad, HoldForm[type]];
    Return[$Failed]
  ];

  Times @@ Join[scalars, components] /. Times[] -> 1
];

contractIndices[sp][DD[qLbar,0][sp[s1]] DD[qL,0][sp[s1]]]


(* ::Subsubsubsection:: *)
(*Main*)


cal[expr_]:=expr/.{qL->Subscript[q, L], qLbar->\!\(\*OverscriptBox[
SubscriptBox[\(q\), \(L\)], \(_\)]\), uR->Subscript[u, R], uRbar->\!\(\*OverscriptBox[
SubscriptBox[\(u\), \(R\)], \(_\)]\), dR->Subscript[d, R], dRbar->\!\(\*OverscriptBox[
SubscriptBox[\(d\), \(R\)], \(_\)]\), F->F, g->\[Gamma], g5->Subscript[\[Gamma], 5], sig->\[Sigma]}


test={DD[qLbar,0][sp[s1]] GA[g][lor[j1], sp[s1,s2]] DD[qL,0][sp[s2]]
DD[qLbar,0][sp[s3]] GA[g][lor[j1], sp[s3,s4]] DD[qL,0][sp[s4]]}
test//readableNotation


test2 = DD[qLbar,0][sp[s1]]GA[g][lor[j1],sp[s1,s2]]DD[qL,0][sp[s2]]*
DD[qLbar,0][sp[s3]] GA[g][lor[j2],sp[s3,s4]]GA[sig][lor[j2, j1],sp[s4,s5]]DD[qL,0][sp[s5]]
test2//readableNotation
test2//contractIndices[sp]//readableNotation
test2//contractIndices[lor]//readableNotation


ClearAll[seeBilinears]
seeBilinears[terms_List]:=seeBilinears/@terms
seeBilinears[term_]:=term//contractIndices[sp]//readableNotation // see


{test[[1]],test2}
%//seeBilinears


(* ::Subsection::Closed:: *)
(*Transpose for error     <--- Run this*)


ClearAll[contractIndices, transposeSymbol, transposeBare, transposeFull, transposeParsed];
contractIndices // allowLists

contractIndices::arity =
  "Each factor may carry at most one outer `1`[...] block, and that block \
may contain at most two indices. Offending factor: `2`.";

contractIndices::bad =
  "The `1`-index factors do not form disjoint non-branching open chains or closed cycles.";

transposeSymbol[s_Symbol] := Symbol[SymbolName[Unevaluated[s]] <> "T"];
transposeSymbol[x_] := x;

transposeBare[expr_] :=
  expr /. HoldPattern[(h_[a_, rest___])[args___]] :>
    h[transposeSymbol[a], rest][args];

transposeFull[type_][expr_] :=
  expr /. HoldPattern[(h_[a_, rest___])[pre___, type[i_, j_], post___]] :>
    h[transposeSymbol[a], rest][pre, type[j, i], post];

transposeParsed[type_][asc_Association] :=
  Association[
    asc,
    "full" -> transposeFull[type][asc["full"]],
    "bare" -> transposeBare[asc["bare"]],
    "idxs" -> Reverse[asc["idxs"]]
  ];

contractIndices[type_][term_] := Module[
  {
    factors, parse, data, scalars, active, singles, mats,
    matsByStart, matsByEnd, singlesByIndex,
    allIndices, localPattern,
    unused, use, openStarts, directPairs, components = {},
    start, seq, current, startIndex, nextMat, nextSingle, grp,
    buildMaps, badQ, info, fixed, candidate, infoCandidate
  },

  factors = timesToList[term];

  parse[expr_] := Replace[
    expr,
    {
      HoldPattern[h_[args___]] :> Module[
        {outer = {args}, blocks, restArgs},
        blocks = Cases[outer, HoldPattern[type[inds___]] :> {inds}, {1}];

        If[
          Length[blocks] > 1 || (blocks =!= {} && Length[First[blocks]] > 2),
          Message[contractIndices::arity, HoldForm[type], HoldForm[expr]];
          Throw[$Failed]
        ];

        restArgs = DeleteCases[outer, HoldPattern[type[___]], {1}];

        <|
          "full" -> expr,
          "bare" -> h[Sequence @@ restArgs],
          "idxs" -> If[blocks === {}, {}, First[blocks]]
        |>
      ],

      other_ :> <|"full" -> other, "bare" -> other, "idxs" -> {}|>
    }
  ];

  data = Catch @ MapIndexed[Append[parse[#1], "id" -> First[#2]] &, factors];
  If[data === $Failed, Return[$Failed]];

  scalars = Lookup[Select[data, #idxs === {} &], "full", {}];
  active  = Select[data, 1 <= Length[#idxs] <= 2 &];
  singles = Select[active, Length[#idxs] == 1 &];
  mats    = Select[active, Length[#idxs] == 2 &];

  If[active === {}, Return[Times @@ scalars /. Times[] -> 1]];

  singlesByIndex = GroupBy[singles, First @ #idxs &];

  buildMaps[mats0_] := Module[{mbs, mbe, ai, lp},
    mbs = GroupBy[mats0, First @ #idxs &];
    mbe = GroupBy[mats0, Last  @ #idxs &];
    ai  = Union[Keys[mbs], Keys[mbe], Keys[singlesByIndex]];

    lp = Function[idx,
      {
        Length @ Lookup[singlesByIndex, idx, {}],
        Length @ Lookup[mbs, idx, {}],
        Length @ Lookup[mbe, idx, {}]
      }
    ];

    <|
      "matsByStart" -> mbs,
      "matsByEnd" -> mbe,
      "allIndices" -> ai,
      "localPattern" -> lp
    |>
  ];

  badQ[assoc_] :=
    AnyTrue[Values[assoc["matsByStart"]], Length[#] > 1 &] ||
    AnyTrue[Values[assoc["matsByEnd"]],   Length[#] > 1 &] ||
    AnyTrue[
      assoc["allIndices"],
      ! MemberQ[{{2,0,0}, {1,1,0}, {1,0,1}, {0,1,1}}, assoc["localPattern"][#]] &
    ];

  info = buildMaps[mats];

  If[badQ[info],
    fixed = Catch[
      Do[
        candidate = ReplacePart[
          mats,
          Thread[pos -> (transposeParsed[type] /@ mats[[pos]])]
        ];
        infoCandidate = buildMaps[candidate];

        If[! badQ[infoCandidate],
          Throw[{candidate, infoCandidate}]
        ],
        {k, 1, Length[mats]},
        {pos, Subsets[Range[Length[mats]], {k}]}
      ];
      $Failed
    ];

    If[fixed === $Failed,
      Message[contractIndices::bad, HoldForm[type]];
      Return[$Failed]
    ];

    mats = fixed[[1]];
    info = fixed[[2]];
  ];

  matsByStart = info["matsByStart"];
  matsByEnd   = info["matsByEnd"];
  allIndices  = info["allIndices"];
  localPattern = info["localPattern"];

  unused = AssociationThread[Lookup[active, "id"], ConstantArray[True, Length[active]]];
  use[id_] := KeyDropFrom[unused, id];

  (* Direct 1-index contractions: a[i] b[i] -> Dot[a,b] *)
  directPairs = Select[allIndices, localPattern[#] === {2,0,0} &];

  Do[
    grp = Lookup[singlesByIndex, idx, {}];
    If[AllTrue[Lookup[grp, "id"], KeyExistsQ[unused, #] &],
      AppendTo[components, Dot @@ Lookup[grp, "bare"]];
      Scan[use, Lookup[grp, "id"]]
    ],
    {idx, directPairs}
  ];

  (* Open chains: start from 1-index factors with pattern {1,1,0} *)
  openStarts = Select[
    singles,
    localPattern[First[#idxs]] === {1,1,0} &
  ];

  Do[
    If[KeyExistsQ[unused, start["id"]],
      seq = {start["bare"]};
      current = First[start["idxs"]];
      use[start["id"]];

      While[True,
        nextSingle = Select[Lookup[singlesByIndex, current, {}], KeyExistsQ[unused, #id] &];
        If[nextSingle =!= {},
          If[Length[nextSingle] =!= 1,
            Message[contractIndices::bad, HoldForm[type]];
            Return[$Failed]
          ];
          AppendTo[seq, First[nextSingle]["bare"]];
          use[First[nextSingle]["id"]];
          Break[]
        ];

        nextMat = Select[Lookup[matsByStart, current, {}], KeyExistsQ[unused, #id] &];
        If[Length[nextMat] =!= 1,
          Message[contractIndices::bad, HoldForm[type]];
          Return[$Failed]
        ];

        nextMat = First[nextMat];
        AppendTo[seq, nextMat["bare"]];
        use[nextMat["id"]];
        current = Last[nextMat["idxs"]];
      ];

      AppendTo[components, Dot @@ seq]
    ],
    {start, openStarts}
  ];

  (* Closed cycles: remaining 2-index factors *)
  Do[
    If[KeyExistsQ[unused, start["id"]],
      seq = {start["bare"]};
      startIndex = First[start["idxs"]];
      current = Last[start["idxs"]];
      use[start["id"]];

      While[current =!= startIndex,
        nextMat = Select[Lookup[matsByStart, current, {}], KeyExistsQ[unused, #id] &];

        If[Length[nextMat] =!= 1,
          Message[contractIndices::bad, HoldForm[type]];
          Return[$Failed]
        ];

        nextMat = First[nextMat];
        AppendTo[seq, nextMat["bare"]];
        use[nextMat["id"]];
        current = Last[nextMat["idxs"]];
      ];

      AppendTo[components, TR @@ seq]
    ],
    {start, mats}
  ];

  If[unused =!= <||>,
    Message[contractIndices::bad, HoldForm[type]];
    Return[$Failed]
  ];

  Times @@ Join[scalars, components] /. Times[] -> 1
];
DD[qLbar,0][sp[s3]] GA[g][lor[j2],sp[s3,s4]]GA[sig][lor[j2, j1],sp[s4,s5]]DD[qL,0][sp[s5]]//contractIndices[sp]
DD[qLbar,0][sp[s3]] GA[g][lor[j2],sp[s3,s4]]GA[sig][lor[j2, j1],sp[s5,s4]]DD[qL,0][sp[s5]]//contractIndices[sp]


(* ::Subsection::Closed:: *)
(*Options  <--- Run this*)


ORDER=6;


(* ::Subsection:: *)
(*Construct possible terms SMEFT - TEST    <--- Run this*)


(* ::Text:: *)
(*We must define these for the purpose of  "IndexPlaceHolder". The point is to store the lorentz and spinor indices of each BB component*)


Clear[nIndicesLor]
nIndicesLor[field_]:=nIndicesLor[field] = Cases[BB,_ field]//First//Exponent[#,iLor]&

Clear[nIndicesSp]
nIndicesSp[field_]:=nIndicesSp[field] = Cases[BB,_ field]//First//Exponent[#,iSpin]&

Clear[nIndicesCol]
nIndicesCol[field_]:=nIndicesCol[field] = Cases[BB,_ field]//First//Exponent[#, iCol]&

Clear[nIndicesIso]
nIndicesIso[field_]:=nIndicesIso[field] = Cases[BB,_ field]//First//Exponent[#, iIso]&

Clear[nIndicesGCol]
nIndicesGCol[field_]:=nIndicesGCol[field] = Cases[BB,_ field]//First//Exponent[#, iGCol]&

Clear[nIndicesPIso]
nIndicesPIso[field_]:=nIndicesPIso[field] = Cases[BB,_ field]//First//Exponent[#, iPIso]&



(* ::Text:: *)
(*Here we define the Building Blocks matrix *)


(*mIndices={}; (*the mindices o jindices are not being used below. It would be best to define sIndices={s[1],s[2],...} and use it*)
(*for contracting terms with more indices (levi civita symbol)*)

(*Building blocks*)
BB = { 
  qL    iSpin^1   iLor^0   iCol^1   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(3)   gtSU2L^2      gtU1Y^(1/6), 
  lL    iSpin^1   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0   dim^(3/2)  gtSU3^0      gtSU2L^2     gtU1Y^(-1/2), 
  uR    iSpin^1   iLor^0   iCol^1   iIso^0 iGCol^0    iPIso^0    dim^(3/2)  gtSU3^3     gtSU2L^0     gtU1Y^(2/3), 
  dR    iSpin^1   iLor^0   iCol^1   iIso^0   iGCol^0  iPIso^0    dim^(3/2)  gtSU3^3     gtSU2L^0     gtU1Y^(-1/3), 
  eR    iSpin^1   iLor^0   iCol^0   iIso^0   iGCol^0  iPIso^0    dim^(3/2)  gtSU3^0     gtSU2L^0     gtU1Y^(-1),
  qLbar iSpin^1   iLor^0   iCol^1   iIso^1   iGCol^0  iPIso^0    dim^(3/2)  gtSU3^(-3)  gtSU2L^(-2)  gtU1Y^(-1/6),
  lLbar iSpin^1   iLor^0   iCol^0   iIso^1   iGCol^0  iPIso^0    dim^(3/2)  gtSU3^0       gtSU2L^(-2)  gtU1Y^(1/2),
  uRbar iSpin^1   iLor^0   iCol^1   iIso^0 iGCol^0    iPIso^0    dim^(3/2)  gtSU3^(-3)   gtSU2L^0     gtU1Y^(-2/3),
  dRbar iSpin^1   iLor^0   iCol^1   iIso^0    iGCol^0 iPIso^0    dim^(3/2)  gtSU3^(-3)  gtSU2L^0      gtU1Y^(1/3),
  eRbar iSpin^1   iLor^0   iCol^0   iIso^0    iGCol^0  iPIso^0    dim^(3/2)  gtSU3^0     gtSU2L^0      gtU1Y^(1),
  (*G    iSpin^0  iLor^2   iCol^0   iIso^0    iGCol^1  iPIso^0    dim^2      gtSU3^0    gtSU2L^0  gtU1Y^0,
  W    iSpin^0  iLor^2   iCol^0     iIso^0    iGCol^0  iPIso^1   dim^2      gtSU3^0    gtSU2L^0  gtU1Y^0,
  B    iSpin^0  iLor^2   iCol^0     iIso^0    iGCol^0  iPIso^0   dim^2      gtSU3^0    gtSU2L^0  gtU1Y^0, *)
 H    iSpin^0  iLor^0   iCol^0      iIso^1    iGCol^0  iPIso^0   dim^1      gtSU3^0    gtSU2L^2  gtU1Y^(1/2),
  Hc   iSpin^0  iLor^0   iCol^0     iIso^1    iGCol^0  iPIso^0   dim^1      gtSU3^0    gtSU2L^(-2)  gtU1Y^(-1/2), 
 sig    iSpin^2   iLor^2   iCol^0   iIso^0    iGCol^0  iPIso^0   dim^0      gtSU3^0      gtSU2L^0     gtU1Y^0, 
 g      iSpin^2   iLor^1   iCol^0   iIso^0    iGCol^0  iPIso^0   dim^0      gtSU3^0       gtSU2L^0     gtU1Y^0,
 g5     iSpin^2   iLor^0   iCol^0   iIso^0    iGCol^0   iPIso^0   dim^0      gtSU3^0      gtSU2L^0     gtU1Y^0,
(* Gll    iSpin^0   iLor^0   iCol^2   iIso^0     iGCol^1  iPIso^0   dim^0      gtSU3^0      gtSU2L^0      gtU1Y^0,
 Pll    iSpin^0   iLor^0   iCol^0   iIso^2     iGCol^0  iPIso^1  dim^0      gtSU3^0      gtSU2L^0      gtU1Y^0,*)
  der    iSpin^0   iLor^1   iCol^0   iIso^0    iGCol^0  iPIso^0   dim^1      gtSU3^0      gtSU2L^0     gtU1Y^0
};
  (*Gll\[Tilde](T^A)_\[Alpha]\[Beta]\:200b*)
  (*Pll\[Tilde](\[Tau]^I)_ij\:200b*)
comb = getCombinations[BB,{3,4,5,6}]//Flatten; (* Create the combinations (minimum 3 terms for dim 6, max 6 terms) *)
Length[comb]*)


(* ::Subsubsection::Closed:: *)
(*BB for Bianchi*)


(*mIndices = {};

(* Bianchi-optimised building blocks *)
(* Only keep gauge field strengths and covariant derivatives. *)
(* This is for testing D_mu X_nu rho + D_nu X_rho mu + D_rho X_mu nu = 0. *)

BBsave = BB;

BB = {
  G    iSpin^0   iLor^2   iCol^0   iIso^0   iGCol^1   iPIso^0   dim^2   gtSU3^0   gtSU2L^0   gtU1Y^0,
  W    iSpin^0   iLor^2   iCol^0   iIso^0   iGCol^0   iPIso^1   dim^2   gtSU3^0   gtSU2L^0   gtU1Y^0,
  B    iSpin^0   iLor^2   iCol^0   iIso^0   iGCol^0   iPIso^0   dim^2   gtSU3^0   gtSU2L^0   gtU1Y^0,

  der  iSpin^0   iLor^1   iCol^0   iIso^0   iGCol^0   iPIso^0   dim^1   gtSU3^0   gtSU2L^0   gtU1Y^0
};

comb = getCombinations[BB, {3, 4, 5, 6}] // Flatten;
Length[comb]*)


(* ::Subsubsection:: *)
(*BB for [COM]*)


(* ::Text:: *)
(*qL only with G field*)


BB = {
  qL     iSpin^1   iLor^0   iCol^1   iIso^1   iGCol^0   iPIso^0   dim^(3/2)   gtSU3^3      gtSU2L^2      gtU1Y^(1/6),
  qLbar  iSpin^1   iLor^0   iCol^1   iIso^1   iGCol^0   iPIso^0   dim^(3/2)   gtSU3^(-3)   gtSU2L^(-2)   gtU1Y^(-1/6),

  G      iSpin^0   iLor^2   iCol^0   iIso^0   iGCol^1   iPIso^0   dim^2       gtSU3^0      gtSU2L^0      gtU1Y^0,
  Gll    iSpin^0   iLor^0   iCol^2   iIso^0   iGCol^1   iPIso^0   dim^0       gtSU3^0      gtSU2L^0      gtU1Y^0,

  g      iSpin^2   iLor^1   iCol^0   iIso^0   iGCol^0   iPIso^0   dim^0       gtSU3^0      gtSU2L^0      gtU1Y^0,
  der    iSpin^0   iLor^1   iCol^0   iIso^0   iGCol^0   iPIso^0   dim^1       gtSU3^0      gtSU2L^0      gtU1Y^0
};
comb = getCombinations[BB,{3,4,5,6}]//Flatten; (* Create the combinations (minimum 3 terms for dim 6, max 6 terms) *)
Length[comb] 


(* ::Subsubsection::Closed:: *)
(*Field strength BB*)


(* ::Text:: *)
(*W*)


(*BB = { 
  qL    iSpin^1   iLor^0   iCol^1   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(3)   gtSU2L^2      gtU1Y^(1/6), 
  lL    iSpin^1   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^0      gtSU2L^2      gtU1Y^(-1/2), 

  qLbar iSpin^1   iLor^0   iCol^1   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(-3)  gtSU2L^(-2)  gtU1Y^(-1/6),
  lLbar iSpin^1   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^0      gtSU2L^(-2)  gtU1Y^(1/2),

  W     iSpin^0   iLor^2   iCol^0   iIso^0  iGCol^0   iPIso^1     dim^2      gtSU3^0      gtSU2L^0      gtU1Y^0,

  H     iSpin^0   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^1      gtSU3^0      gtSU2L^2      gtU1Y^(1/2),
  Hc    iSpin^0   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^1      gtSU3^0      gtSU2L^(-2)  gtU1Y^(-1/2),

  Pll   iSpin^0   iLor^0   iCol^0   iIso^2  iGCol^0   iPIso^1     dim^0      gtSU3^0      gtSU2L^0      gtU1Y^0,

  g     iSpin^2   iLor^1   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^0      gtSU3^0      gtSU2L^0      gtU1Y^0,
  der   iSpin^0   iLor^1   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^1      gtSU3^0      gtSU2L^0      gtU1Y^0
};
comb = getCombinations[BB,{3,4,5,6}]//Flatten; (* Create the combinations (minimum 3 terms for dim 6, max 6 terms) *)
Length[comb] *)


(* ::Text:: *)
(*G*)


(*BB = { 
  qL    iSpin^1   iLor^0   iCol^1   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(3)   gtSU2L^2      gtU1Y^(1/6), 
  uR    iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^3      gtSU2L^0      gtU1Y^(2/3), 
  dR    iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^3      gtSU2L^0      gtU1Y^(-1/3), 

  qLbar iSpin^1   iLor^0   iCol^1   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(-3)  gtSU2L^(-2)  gtU1Y^(-1/6),
  uRbar iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(-3)  gtSU2L^0      gtU1Y^(-2/3),
  dRbar iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(-3)  gtSU2L^0      gtU1Y^(1/3),

  G     iSpin^0   iLor^2   iCol^0   iIso^0  iGCol^1   iPIso^0     dim^2      gtSU3^0      gtSU2L^0      gtU1Y^0,

  Gll   iSpin^0   iLor^0   iCol^2   iIso^0  iGCol^1   iPIso^0     dim^0      gtSU3^0      gtSU2L^0      gtU1Y^0,

  g     iSpin^2   iLor^1   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^0      gtSU3^0      gtSU2L^0      gtU1Y^0,
  der   iSpin^0   iLor^1   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^1      gtSU3^0      gtSU2L^0      gtU1Y^0
};
comb = getCombinations[BB,{3,4,5,6}]//Flatten; (* Create the combinations (minimum 3 terms for dim 6, max 6 terms) *)
Length[comb] *)


(* ::Text:: *)
(*B munu*)


(*BB = { 
  qL    iSpin^1   iLor^0   iCol^1   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(3)   gtSU2L^2      gtU1Y^(1/6), 
  lL    iSpin^1   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^0      gtSU2L^2      gtU1Y^(-1/2), 
  uR    iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^3      gtSU2L^0      gtU1Y^(2/3), 
  dR    iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^3      gtSU2L^0      gtU1Y^(-1/3), 
  eR    iSpin^1   iLor^0   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^0      gtSU2L^0      gtU1Y^(-1),

  qLbar iSpin^1   iLor^0   iCol^1   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(-3)  gtSU2L^(-2)  gtU1Y^(-1/6),
  lLbar iSpin^1   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^0      gtSU2L^(-2)  gtU1Y^(1/2),
  uRbar iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(-3)  gtSU2L^0      gtU1Y^(-2/3),
  dRbar iSpin^1   iLor^0   iCol^1   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^(-3)  gtSU2L^0      gtU1Y^(1/3),
  eRbar iSpin^1   iLor^0   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^(3/2)  gtSU3^0      gtSU2L^0      gtU1Y^(1),

  B     iSpin^0   iLor^2   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^2      gtSU3^0      gtSU2L^0      gtU1Y^0,

  H     iSpin^0   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^1      gtSU3^0      gtSU2L^2      gtU1Y^(1/2),
  Hc    iSpin^0   iLor^0   iCol^0   iIso^1  iGCol^0   iPIso^0     dim^1      gtSU3^0      gtSU2L^(-2)  gtU1Y^(-1/2),

  g     iSpin^2   iLor^1   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^0      gtSU3^0      gtSU2L^0      gtU1Y^0,
  der   iSpin^0   iLor^1   iCol^0   iIso^0  iGCol^0   iPIso^0     dim^1      gtSU3^0      gtSU2L^0      gtU1Y^0
};
comb = getCombinations[BB,{3,4,5,6}]//Flatten; (* Create the combinations (minimum 3 terms for dim 6, max 6 terms) *)
Length[comb] *)


(* ::Text:: *)
(**)


(* ::Subsubsection::Closed:: *)
(*making first basis*)


selected = Select[comb,
  (EvenQ[Exponent[#,iLor]]) &&
  (EvenQ[Exponent[#,iSpin]]) &&
  (EvenQ[Exponent[#,iCol]]) &&
  (EvenQ[Exponent[#,iIso]]) &&
  (EvenQ[Exponent[#,iPIso]]) &&
  (EvenQ[Exponent[#,iGCol]]) &&
  Exponent[#,dim] == ORDER &&
  !MatchQ[#, (gtSU3|gtSU3^_)_] &&
  !MatchQ[#, (gtSU2L|gtSU2L^_)_] &&
  !MatchQ[#, (gtU1Y|gtU1Y^_)_] &
];


Bc = selected /. {iSpin -> 1, iLor -> 1, dim -> 1, iCol -> 1, iIso ->1, iPIso ->1, iGCol ->1} // DeleteCases[der^_] // DeleteDuplicates;
Length[Bc]
Bc[[1;;10]] // see;



(* ::Text:: *)
(*Now we would like to insert the index places and derivatives. *)


Clear[insertIndexPlaceHoldersGeneral, insertIndexPlaceHoldersAddDerivatives]

(*if Lor indices: count the derivatives on DD*)
insertIndexPlaceHoldersAddDerivatives[numberIndices_][Y__][expr_]:= (expr/.
{((head:Alternatives@@{Y})[matrix_,nder_:0][other___]):>head[matrix,nder][other,index[nder+numberIndices[matrix]]],
((head:Alternatives@@{Y})[matrix_,nder_:0]):>head[matrix,nder][index[nder+numberIndices[matrix]]]})

(*if any other type: do not count derivatives as extra amout of indices*)
insertIndexPlaceHoldersGeneral[numberIndices_][Y__][expr_]:= (expr/.
{((head:Alternatives@@{Y})[matrix_,nder_:0][other___]):>head[matrix,nder][other,index[numberIndices[matrix]]],
((head:Alternatives@@{Y})[matrix_,nder_:0]):>head[matrix,nder][index[numberIndices[matrix]]]})


(Bc/.{g->GA[g], g5->GA[g5], sig->GA[sig], Gll->GA[Gll], Pll->GA[Pll]});
%//applyDerivativesOn[{qL, qLbar, lL, lLbar, uR, uRbar, dR, dRbar, eR, eRbar, G, B, W, H, Hc}];
%//insertIndexPlaceHoldersAddDerivatives[nIndicesLor][DD, GA]; (*MISTAKE HERE: GA has now a zero in the second argument; fixed readableNotation above to handle it. But dirty trick*)
%/.index[n_]:>lor[index[n]]//showLength;
%//insertIndicesOfType[{j1,j2,j3,j4, j5, j6}]//showLength;



fb1=%/.A_[a___,lor[],b___]:>A[a,b];


%//insertIndexPlaceHoldersGeneral[nIndicesSp][DD, GA]//showLength;
%/.index[n_]:>sp[index[n]];
%//insertIndicesOfType[{s1,s2,s3,s4,s5,s6}]//showLength // showTiming;


fb2=%/.A_[a___,sp[],b___]:>A[a,b];


%//insertIndexPlaceHoldersGeneral[nIndicesCol][DD, GA] // showLength;
%/.index[n_] :> col[index[n]];
%//insertIndicesOfType[{c1, c2, c3, c4,c5,c6}] // showLength // showTiming;


fb3=%/.A_[a___,col[],b___]:>A[a,b];


%//insertIndexPlaceHoldersGeneral[nIndicesIso][DD, GA] // showLength;
%/.index[n_] :> iso[index[n]];
%//insertIndicesOfType[{i1, i2, i3, i4, i5, i6}] // showLength // showTiming;


fb4=%/.A_[a___,iso[],b___]:>A[a,b];


%//insertIndexPlaceHoldersGeneral[nIndicesGCol][DD, GA] // showLength;
%/.index[n_] :> gcol[index[n]];
%//insertIndicesOfType[{d1, d2, d3, d4}] // showLength // showTiming;


fb5=%/.A_[a___,gcol[],b___]:>A[a,b];


%//insertIndexPlaceHoldersGeneral[nIndicesPIso][DD, GA] // showLength;
%/.index[n_] :> piso[index[n]];
%//insertIndicesOfType[{f1, f2, f3, f4}] // showLength // showTiming;


firstbasis=%/.A_[a___,piso[],b___]:>A[a,b];


(* ::Text:: *)
(*Now apply the contraction [Comented out to accelerate. contractIndices[sp] is just a helper to visualize . FB not used later]*)


(*FB = firstbasis // contractIndices[sp] // readableNotation; (*// MapIndexed[{#2[[1]], #1} &, #] & // Grid*)*)


(*Length[FB]
Length[firstbasis]
FB[[400;;410]]; 
firstbasis[[400;;410]]
%// MapIndexed[{#2[[1]], #1} &, #] & // Grid // EchoFunction[readableNotation]*)


Export[FileNameJoin[{$HomeDirectory, "Downloads", "firstbasis.txt"}], firstbasis, "Table"]


(* ::Subsection::Closed:: *)
(*Trivial relations SMEFT     <--- Run this*)


(* ::Subsubsection::Closed:: *)
(*Canonicalize SMEFT + Easy Zeros*)


(* ::Text:: *)
(*Most important - shuffle dummy indices (shuffle indices to reduce the repeating terms)*)


(* Index Renaming rename indices like s7,s9 into s1,s2 etc  *)
ClearAll[renameIndexFamily];

renameIndexFamily[expr_, head_Symbol, prefix_String] := Module[
  {old, flatOld, new, rules},
  
    (* grab all indices sitting inside 'head' *)
  old = Cases[
    Unevaluated[expr],
    head[args__] :> {args},
    Infinity
  ];

  (* flatten and remove repeats *)
  flatOld = DeleteDuplicates @ Flatten[old];

  (* nothing to do if this index type is not there *)
  If[flatOld === {}, Return[expr]];

  (* make fresh canonical names like s1,s2 or c1,c2 *)
  new = Array[Symbol[prefix <> ToString[#]] &, Length[flatOld]];
  rules = Thread[flatOld -> new];

  (* replace inside this specific index family *)
  expr /. head[args__] :> head @@ ({args} /. rules)
];




(* Tensor Canonicalization (fix simple tensor ordering stuff )*)
ClearAll[canonicalizeTensorIndicesSafe];

canonicalizeTensorIndicesSafe[expr_] := expr //. {

  (* Isospin tensor *)
  HoldPattern[GA[Pll, 0][iso[a_, b_], rest___]] :> GA[Pll, 0][iso @@ Sort[{a, b}], rest],

  (* Color tensor *)
  HoldPattern[GA[Gll, 0][col[a_, b_], rest___]] :> GA[Gll, 0][col @@ Sort[{a, b}], rest]

};



(* Tensor Canonicalization (Lorentz) - fix Lorentz ordering *)
ClearAll[canonicalizeTensorIndicesLorentz];

canonicalizeTensorIndicesLorentz[expr_] := expr //. {

HoldPattern[GA[sig, 0][pre___, lor[mu_, nu_], post___]] /; !OrderedQ[{mu, nu}] :> -GA[sig, 0][pre, lor[nu, mu], post]


};


ClearAll[canonicalizeOneG];

canonicalizeOneG[expr_] := expr /. {

  (* plain field strength X_{mu nu}, where X = G, W, B *)
HoldPattern[DD[field : (G | W | B), 0][lor[mu_, nu_], rest___]] :> Signature[{mu, nu}] * DD[field, 0][lor @@ Sort[{mu, nu}], rest],

(* DD X_{mu nu}: antisymmetry only in the final field-strength pair *)
HoldPattern[DD[field : (G | W | B), n_Integer?Positive][lor[idx___], rest___]] :>
  Module[{all = {idx}, der, fs},
    der = Drop[all, -2];
    fs  = Take[all, -2];
    If[Length[all] =!= n + 2,
      DD[field, n][lor[idx], rest],
      If[fs[[1]] === fs[[2]],
        0,
        Signature[fs] * DD[field, n][lor @@ Join[der, Sort[fs]], rest]
      ]
    ]
  ]
};


(* fix spinor ordering in gamma/sigma*)

canonicalizeTensorIndicesSpinor[expr_] := expr //. {

  (* gamma_mu symmetric in spinor slots, but choose descending convention *)
  HoldPattern[GA[g, x___][pre___, sp[a_, b_], post___]] /; 
    OrderedQ[{a, b}] && a =!= b :> GA[g, x][pre, sp[b, a], post],

  HoldPattern[GA[g5, x___][pre___, sp[a_, b_], post___]] /; 
    ! OrderedQ[{a, b}] :> -GA[g5, x][pre, sp[b, a], post],

  HoldPattern[GA[sig, x___][pre___, sp[a_, b_], post___]] /; 
    ! OrderedQ[{a, b}] :> -GA[sig, x][pre, sp[b, a], post]
};


(* Full Tensor Canonicalization *)
ClearAll[canonicalizeTensorIndices];

canonicalizeTensorIndices[expr_] :=
  expr //
  canonicalizeTensorIndicesSafe //
  canonicalizeTensorIndicesLorentz //
  canonicalizeOneG //
  canonicalizeTensorIndicesSpinor;


(* make a rough \[OpenCurlyDoubleQuote]skeleton\[CloseCurlyDoubleQuote] of a factor so sorting is stable *)
ClearAll[indexSkeleton, factorSortKey, sortFields];

indexSkeleton[expr_] := expr /. {
   sp[__]   :> sp[],
   col[__]  :> col[],
   iso[__]  :> iso[],
   lor[__]  :> lor[],
   piso[__] :> piso[],
   gcol[__] :> gcol[]
};

factorSortKey[x_] := {
  If[MatchQ[x, _DD], 1, 2],
  ToString[Head[x], InputForm],
  ToString[indexSkeleton[x], InputForm]
};

sortFields[expr_] := Module[{factors},
  factors = If[Head[expr] === Times, List @@ expr, {expr}];
  Times @@ SortBy[factors, factorSortKey]
];


ClearAll[fieldStrengthRepeatedLorentzZeroQ];

fieldStrengthRepeatedLorentzZeroQ[n_Integer?NonNegative, inds_List] := Module[
  {fs},
  
  (* Field strength should have n derivative indices + 2 antisymmetric indices *)
  If[Length[inds] =!= n + 2, Return[False]];
  
  (* Only the final two indices belong to B_mu_nu, W_mu_nu, G_mu_nu *)
  fs = Take[inds, -2];
  
  fs[[1]] === fs[[2]]
];


ClearAll[removeEasyZeroes];

removeEasyZeroes[expr_] := expr //. {

  (* sigma Lorentz antisymmetry => zero when indices equal *)
  HoldPattern[GA[sig, 0][pre___, lor[a_, a_], post___]] :> 0,

  (* repeated spinor pair inside antisymmetric structures *)
  HoldPattern[GA[sig, 0][pre___, sp[a_, a_], post___]] :> 0,
  HoldPattern[GA[g5, 0][pre___, sp[a_, a_], post___]]  :> 0,

  (* gamma_mu with identical spinor pair *)
  HoldPattern[GA[g, _][pre___, sp[a_, a_], post___]] :> 0,

  (* field strength antisymmetry *)
  HoldPattern[DD[field : (G | W | B), n_Integer?NonNegative][pre___, lor[inds___], post___]] /; fieldStrengthRepeatedLorentzZeroQ[n, {inds}] :> 0,
  
  HoldPattern[GA[Gll, 0][pre___, col[a_, a_], post___]] :> 0,
  HoldPattern[GA[Pll, 0][pre___, iso[a_, a_], post___]] :> 0
};





ClearAll[renameIndexFamilyByName];

renameIndexFamilyByName[expr_, head_Symbol, prefix_String] := Module[
  {old, new, rules},

  old = DeleteDuplicates @ SortBy[
     Flatten @ Cases[
       Unevaluated[expr],
       head[args__] :> {args},
       Infinity
     ],
     ToString[#, InputForm] &
   ];

  If[old === {}, Return[expr]];

  new = Array[Symbol[prefix <> ToString[#]] &, Length[old]];
  rules = Thread[old -> new];

  expr /. head[args__] :> head @@ ({args} /. rules)
];


(* Main *)
ClearAll[canonicalizeDummyIndices];

Attributes[canonicalizeDummyIndices]={Listable}

canonicalizeDummyIndices[term_] := Module[{aux = term},
  aux = removeEasyZeroes[aux];
  aux = sortFields[aux];
  aux = canonicalizeTensorIndices[aux];

  aux = renameIndexFamilyByName[aux, sp, "s"];
  aux = renameIndexFamily[aux, col,  "c"];
  aux = renameIndexFamily[aux, iso,  "i"];
  aux = renameIndexFamily[aux, lor,  "j"];
  aux = renameIndexFamily[aux, piso, "f"];
  aux = renameIndexFamily[aux, gcol, "d"];

  aux = canonicalizeTensorIndices[aux];
  aux = removeEasyZeroes[aux];
  aux = sortFields[aux];

  aux
];


(* Here we just remove "-"*)

ClearAll[normalizeOverallSign];

Attributes[normalizeOverallSign]={Listable};

normalizeOverallSign[expr_] := Module[{e = Expand[expr]},
  If[Head[e] === Times && First[List @@ e] === -1,
    -e,
    e
  ]
];


(*Now this cell is in the main*)

ClearAll[firstbasisCanon, TrBasis1, duplicateClasses];

firstbasisCanon = DeleteCases[
  normalizeOverallSign @ canonicalizeDummyIndices[#] & /@ firstbasis,
  0
];

TrBasis1 = DeleteDuplicates[firstbasisCanon];

Length[firstbasis]
Length[firstbasisCanon]
Length[TrBasis1]

duplicateClasses = Select[
  GatherBy[firstbasis, canonicalizeDummyIndices],
  Length[#] > 1 &
];
Length[duplicateClasses]


Export[FileNameJoin[{$HomeDirectory, "Downloads", "TrBasis1.txt"}], TrBasis1, "Table"]


(* ::Subsubsection::Closed:: *)
(*Local trivial algebra SMEFT*)


(* ::Text:: *)
(*Reduce the list of possibleTerms accounting for trivial relations:  (1) remove easy zeroes following from definitions;  (2) generate all possible shapes of each term, sort them, save first shape of each term, delete duplicates; (2.0) accelerate this doing it first with generateAlternativeShapesQuick; (3) remove terms that are symmetric and antisymmetric on some index permutation.*)
(**)
(*time P8: 18'+10'+5' = 33' (laptop) 11' (desktop)*)


ClearAll[ApplyTrivial]
Attributes[ApplyTrivial] = {Listable};

ApplyTrivial[expr_] := expr //. {
  (* gamma5 *)
  GA[g5, 0][a1___, sp[s1_,s2_], a2___]  GA[g5, 0][b1___, sp[s2_,s3_],b2___] :> 1,
  (*Thee next function is now written correctly, but it fails because it enters in an infinite loop *)
  GA[g5, 0][a1___, sp[s1_,s2_], a2___]  GA[g, 0][b1___, sp[s2_,s3_],b2___] :> -GA[g, 0][b1,sp[s1,s2],b2]  GA[g5, 0][a1,sp[s2,s3],a2],
  
  (*gamma matrices contraction*)
  HoldPattern[GA[g, 0][lor[mu_], sp[a_, b_]] * GA[g, 0][lor[mu_], sp[b_, a_]]] :> 4
};



TrBasis2 = DeleteCases[ApplyTrivial /@ TrBasis1, 0];


Length[TrBasis2]


Export[FileNameJoin[{$HomeDirectory, "Downloads", "TrBasis2.txt"}], TrBasis2, "Table"]


(* ::Text:: *)
(*Canonicalize again*)


(* ::Text:: *)
(*// DeleteDuplicates;*)


(*Error?*)

(*TrBasis3 = TrBasis2 // Map[canonicalizeDummyIndices] // DeleteDuplicates;*)


(*Export[FileNameJoin[{$HomeDirectory, "Downloads", "TrBasis3.txt"}], TrBasis3, "Table"]*)


(* ::Subsubsection::Closed:: *)
(*Chirality v2  SMEFT*)


Clear[chiralityTag]

chiralityTag[x_] := Switch[x,
  lL | qL, "L",
  lLbar | qLbar, "Lbar",
  eR | uR | dR, "R",
  eRbar | uRbar | dRbar, "Rbar",
  _, None
];


Clear[operatorChiralityTags]

operatorChiralityTags[op_] := Cases[op, DD[field_, ___][___] :> chiralityTag[field], Infinity];


(* ::Text:: *)
(*The "PR" "PL" operators change when they "go through" gamma, but don't see g5 and sigma*)


Clear[gammaParityOfGA]

gammaParityOfGA[ga_] := Which[
  MatchQ[ga, HoldPattern[GA[g, ___][___]]], 1,
  MatchQ[ga, HoldPattern[GA[g5, ___][___]]], 0,
  MatchQ[ga, HoldPattern[GA[sig, ___][___]]], 0,
  True, 0
];


(* ::Text:: *)
(*Go through the expression and grab all fermions independently. f.e we store qL as: name, spinor label, and chirality :*)
(**)
(*qL: 		<|Field->qL,Spinor->s1,Chirality->L|>,<|Field->qLbar,Spinor->s2,Chirality->Lbar|>*)


Clear[fermionSpinorData]

fermionSpinorData[expr_] := Cases[
  expr,
  HoldPattern[DD[f_, ___][pre___, sp[s_], post___]] :> <|
    "Field" -> f,
    "Spinor" -> s,
    "Chirality" -> chiralityTag[f]
  |>,
  Infinity
];


(* ::Text:: *)
(*The "ChiralityScalar" checks the Chirality for no-g elements. In the output "False" mean "keep it; nonzero"*)


ClearAll[ChiralityScalar];

ChiralityScalar[expr_] := Module[
  {fermions, gammaSpins, scalarFermions, groups, badPairQ},

  fermions = fermionSpinorData[expr];
  If[fermions === {}, Return[Nofermions]];

  gammaSpins = DeleteDuplicates @ Flatten[
    gammaSpinorData[expr][[All, "Spinors"]] /. Missing[_, _] -> {}
  ];

  scalarFermions = Select[
    fermions,
    ! MemberQ[gammaSpins, #["Spinor"]] &
  ];

  If[scalarFermions === {}, Return[False]];

  groups = GatherBy[scalarFermions, #["Spinor"] &];

 badPairQ[group_] := Module[
  {tags = Sort[DeleteCases[group[[All, "Chirality"]], None]]},

  tags === Sort[{"L", "L"}] ||
  tags === Sort[{"Lbar", "Lbar"}] ||
  tags === Sort[{"L", "Lbar"}] ||

  tags === Sort[{"R", "R"}] ||
  tags === Sort[{"Rbar", "Rbar"}] ||
  tags === Sort[{"R", "Rbar"}]
];

  AnyTrue[groups, badPairQ]
];


(* ::Text:: *)
(*The "gammaSpinorData" scans the operator and extracts gamma matrices. Which gamma matrix is present, which two spinor indices does it connect, and is it odd or even? For example, an operator containing one gamma is:*)
(**)
(*<|GAExpr->GA[g,0][lor[mu],sp[s1,s2]],Head->g,Spinors->{s1,s2},Parity->1|>*)
(**)


Clear[gammaSpinorData]

gammaSpinorData[expr_] := Cases[
  expr,
  HoldPattern[
    ga : GA[head : (g | g5 | sig), ___][pre___, sp[a_, b_], post___]
  ] :> <|
    "GAExpr" -> HoldForm[ga],
    "Head" -> head,
    "Spinors" -> {a, b},
    "Parity" -> gammaParityOfGA[ga]
  |>,
  Infinity
];


(* ::Text:: *)
(*This makes a map from spinor index to chirality. For example,  if the expression contains L[s1] Lbar[s2] we get:*)
(**)
(*		"<|s1 -> "L", s2 -> "Lbar"|>"*)


(*Labels each spinor*)
spinorToChiralityRules[expr_] := Module[{fermions},
  fermions = fermionSpinorData[expr];
  Association @ Cases[
    fermions,
    x_ /; x["Chirality"] =!= None :> (x["Spinor"] -> x["Chirality"])
  ]
];


(* ::Text:: *)
(*The "ChiralityforOne" checks one gamma bilinear and decides whether it is zero. It takes the number that emerges from parity testing and only leave the operators that give odd/even number (f.e gamma is 1 due to parity as defined above). For same chirality objects odd structures survive; for different chirality even.*)


ClearAll[ChiralityforOne];

ChiralityforOne[gaAssoc_, spinMap_] := Module[
  {a, b, ca, cb, parityMod2, tags},

  {a, b} = gaAssoc["Spinors"];
  ca = Lookup[spinMap, a, None];
  cb = Lookup[spinMap, b, None];
  parityMod2 = gaAssoc["Parity"];

  If[ca === None || cb === None, Return[False]];

  tags = Sort[{ca, cb}];

  Which[
    tags === Sort[{"L", "L"}] || 
    tags === Sort[{"Lbar", "Lbar"}] ||
    tags === Sort[{"R", "R"}] ||
    tags === Sort[{"Rbar", "Rbar"}],
      True,

    tags === Sort[{"Lbar", "L"}] || 
    tags === Sort[{"Rbar", "R"}],
      EvenQ[parityMod2],

    tags === Sort[{"Lbar", "R"}] || 
    tags === Sort[{"Rbar", "L"}],
      OddQ[parityMod2],

    True,
      False
  ]
];





(* ::Text:: *)
(*The "ChiralityOne" does the same thing as the "ChiralityScalar" but for stuff containing gammas*)


Clear[ChiralityOne]

ChiralityOne[expr_] := Module[
  {spinMap, gammas},

  gammas = gammaSpinorData[expr];

  If[gammas === {}, Return[NoGamma]];

  spinMap = spinorToChiralityRules[expr];

  AnyTrue[gammas, ChiralityforOne[#, spinMap] &]
];


ClearAll[ChiralityGammaChains];

ChiralityGammaChains[expr_] := Module[
  {fermions, spinMap, gammas, edges, graph, fspins, comps, badCompQ},

  fermions = fermionSpinorData[expr];
  spinMap = spinorToChiralityRules[expr];
  gammas = gammaSpinorData[expr];

  If[gammas === {}, Return[False]];

  edges = gammas /. a_Association :>
     UndirectedEdge @@ a["Spinors"];

  graph = Graph[edges];

  fspins = Keys[spinMap];
  comps = ConnectedComponents[graph];

  badCompQ[comp_] := Module[
    {ends, tags, parity},

    ends = Intersection[comp, fspins];

    If[Length[ends] != 2, Return[True]];

    tags = Sort[Lookup[spinMap, ends]];
    parity = Mod[
      Total[
        Cases[
          gammas,
          a_ /; SubsetQ[comp, a["Spinors"]] :> a["Parity"]
        ]
      ],
      2
    ];

    Which[
      tags === Sort[{"L", "L"}] ||
      tags === Sort[{"Lbar", "Lbar"}] ||
      tags === Sort[{"R", "R"}] ||
      tags === Sort[{"Rbar", "Rbar"}],
        EvenQ[parity],

      tags === Sort[{"Lbar", "L"}] ||
      tags === Sort[{"Rbar", "R"}],
        EvenQ[parity],

      tags === Sort[{"Lbar", "R"}] ||
      tags === Sort[{"Rbar", "L"}],
        OddQ[parity],

      True,
        False
    ]
  ];

  AnyTrue[comps, badCompQ]
];


(* ::Text:: *)
(*Final wrapper (removes the ones that came out to be Chirality-Bad*)


ClearAll[ChiralityZero, removeZeroChirality];

ChiralityZero[op_] :=
  TrueQ[ChiralityScalar[op]] ||
  TrueQ[ChiralityOne[op]] ||
  TrueQ[ChiralityGammaChains[op]];

removeZeroChirality[list_List] := DeleteCases[list, op_ /; ChiralityZero[op]];

removeZeroChirality[op_] :=  If[ChiralityZero[op], 0, op];


(* ::Text:: *)
(*The following code had to be added because of terms that contain gamma matrices that do not contract with fermions. F.e*)
(* *)
(*"lL[sp1, sp2] g[sp1, sp2] g[sp3,sp4] g[sp3,sp4]" (the 2 gammas are "contracted" with each other)*)


ClearAll[fermionSpinors, gammaSpinorPairs, badGammaChainQ];

fermionSpinors[op_] := DeleteDuplicates @ Cases[
  op,
  HoldPattern[DD[_, ___][___, sp[s_], ___]] :> s,
  Infinity
];

gammaSpinorPairs[op_] := Cases[
  op,
  HoldPattern[GA[g | g5 | sig, ___][___, sp[a_, b_], ___]] :> {a, b},
  Infinity
];

badGammaChainQ[op_] := Module[
  {fspin, gspin},

  fspin = fermionSpinors[op];
  gspin = DeleteDuplicates @ Flatten[gammaSpinorPairs[op]];

  Complement[gspin, fspin] =!= {}
];


ClearAll[badGammaChainQ, fermionSpinors, gammaSpinorPairs];

fermionSpinors[op_] := DeleteDuplicates @ Cases[
  op,
  HoldPattern[DD[_, ___][___, sp[s_], ___]] :> s,
  Infinity
];

gammaSpinorPairs[op_] := Cases[
  op,
  HoldPattern[GA[g | g5 | sig, ___][___, sp[a_, b_], ___]] :> {a, b},
  Infinity
];

badGammaChainQ[op_] := Module[
  {fspin, pairs, components, badComponents},

  fspin = fermionSpinors[op];
  pairs = gammaSpinorPairs[op];

  If[pairs === {}, Return[False]];

  components = ConnectedComponents[Graph[UndirectedEdge @@@ pairs]];

  badComponents = Select[
    components,
    Intersection[#, fspin] === {} &
  ];

  badComponents =!= {}
];


ClearAll[Chirality];

Chirality[op_] := If[badGammaChainQ[op] || ChiralityZero[op],0,op];


TrBasis30 = removeZeroChirality[TrBasis2];
TrBasis3 = DeleteCases[Chirality /@ TrBasis30, 0];

Length[TrBasis30]
Length[TrBasis3]


Export[FileNameJoin[{$HomeDirectory, "Downloads", "TrBasis30.txt"}], TrBasis30, "Table"]


Export[FileNameJoin[{$HomeDirectory, "Downloads", "TrBasis3.txt"}], TrBasis3, "Table"]


(* ::Subsubsection::Closed:: *)
(*Tests generatealt*)


(* ::Text:: *)
(*The "indicesofType" and "dummyIndicesOfType" grab the indices in the expression. F.e 	 DD[B, 1][lor[j1, j1, j2]];*)
(**)
(*indicesOfType[lor][] = {j1, j1, j2}*)
(*dummyIndicesOfType[lor][] = {j1 j2}*)


ClearAll[indicesOfType]

(* grab all indices that appear inside one index head *)
indicesOfType[iType_][term_] := Flatten @ Cases[term, iType[args___] :> {args}, Infinity];


indicesOfType[lor][t3]


ClearAll[dummyIndicesOfType]

dummyIndicesOfType[iType_][term_] := Sort @ DeleteDuplicates[indicesOfType[iType][term]];


dummyIndicesOfType[lor][t3]


(* ::Text:: *)
(*Replace dummy indices oftype by indicesoftype + deleteduplicates. What it does is, takes an operator and permutes all of the indices. The:*)
(**)
(*	DD[B, 0][lor[j1, j2]] DD[B, 0][lor[j1, j2]]; 	 --->		{DD[B,0][lor[j1,j2]]DD[B,0][lor[j1,j2]]    ,    DD[B,0][lor[j2,j1]]DD[B,0][lor[j2,j1]]}*)
(*	*)
(*	DD[B, 1][lor[j1, j2, j3]];	    --->	{DD[B,1][lor[j1,j2,j3]]  ,	DD[B,1][lor[j1,j3,j2]]	,	DD[B,1][lor[j2,j1,j3]],	DD[B,1][lor[j2,j3,j1]]		,	DD[B,1][lor[j3,j1,j2]],	DD[B,1][lor[j3,j2,j1]]}*)


ClearAll[shuffleDummyIndicesOfType]

(* generate all allowed renamings of dummy indices of one family *)
shuffleDummyIndicesOfType[iType_][term_] := 
  Module[{idx, permIndices},
    idx = dummyIndicesOfType[iType][term];
    If[idx === {}, Return[{term}]];
    
    permIndices = Permutations[idx];
    
    Table[
      term /. Thread[idx -> permIndices[[i]]],
      {i, Length[permIndices]}
    ]
  ];


shuffleDummyIndicesOfType[lor][t2]


(* ::Text:: *)
(*The "normalizeUnsignedShape" removes the "sign" in the expression*)


ClearAll[normalizeUnsignedShape]
(* unsigned cleanup: expand, remove only overall numbers, forget sign symbol *)
normalizeUnsignedShape[expr_] := expr // Expand // ignoreSigns;


(* ::Text:: *)
(*This part "swapIndicesFG"  uses the anticommutation of the strength tensors (G,W,B). So DD[G,0][lor[j1,j2]] ---> DD[G,0][lor[j1,j2]] + signDD[G,0][lor[j2,j1]]*)


ClearAll[swapIndicesFG]

(* antisymmetry of field strengths *)
swapIndicesFG[expr_] := Module[{tmp},
  tmp = expr /. 
    DD[f:(G|W|B), n_][a1___, lor[iPrev___, x_, y_], a2___] :>(DD[f, n][a1, lor[iPrev, x, y], a2] + sign DD[f, n][a1, lor[iPrev, y, x], a2]) /; x =!= y;

  plusToList[Expand[tmp]]
];



(* ::Text:: *)
(*This part "swapIndicessig"  uses the anticommutation of the sigma. So GA[sig,0][lor[j1,j2]] ---> 	GA[sig,0][lor[j1,j2]] 	+ 	sign GA[sig,0][lor[j2,j1]]*)


ClearAll[swapIndicessig]

(* antisymmetry of sigma_{mu nu} if sig is activated later *)
swapIndicessig[expr_] := Module[{tmp},
  tmp = expr /. 
    GA[sig, n_][a1___, lor[iPrev___, x_, y_], a2___] :>
      (
        GA[sig, n][a1, lor[iPrev, x, y], a2] +
        sign GA[sig, n][a1, lor[iPrev, y, x], a2]
      ) /; x =!= y;

  plusToList[Expand[tmp]]
];


(* ::Text:: *)
(*The "applyAlternativeShapeRules" usese the two above functions and delete duplicates*)


ClearAll[applyAlternativeShapeRules]

(* apply all explicit symmetry/antisymmetry rules *)
applyAlternativeShapeRules[terms_List] := Module[{aux = terms},
  aux = Flatten[swapIndicesFG /@ aux];
  aux = Flatten[swapIndicessig /@ aux];
  DeleteDuplicates[aux]
];


applyAlternativeShapeRules[t1t]


(* ::Text:: *)
(*The main:*)


(* generateAlternativeShapes for the full BB*)
ClearAll[generateAlternativeShapes]

generateAlternativeShapes[term_] := Module[{aux},

  aux = {term};

  (* explicit symmetry / antisymmetry relations *)
  aux = applyAlternativeShapeRules[aux];

  (* dummy-index relabelings, one family at a time *)
  aux = Flatten[shuffleDummyIndicesOfType[lor]  /@ aux] // DeleteDuplicates;
  aux = Flatten[shuffleDummyIndicesOfType[col]  /@ aux] // DeleteDuplicates;
  aux = Flatten[shuffleDummyIndicesOfType[iso]  /@ aux] // DeleteDuplicates;
  aux = Flatten[shuffleDummyIndicesOfType[gcol] /@ aux] // DeleteDuplicates;
  aux = Flatten[shuffleDummyIndicesOfType[piso] /@ aux] // DeleteDuplicates;
  aux = Flatten[shuffleDummyIndicesOfType[sp]   /@ aux] // DeleteDuplicates;

  (* unsigned normalization *)
  aux = normalizeUnsignedShape /@ aux;
  aux = DeleteDuplicates[aux];

  (* keep original term first *)
  DeleteDuplicates @ Prepend[aux, term]
];


ClearAll[canonicalShape];

canonicalShape[term_] := First @ SortBy[
  generateAlternativeShapes[term],
  ToString[InputForm[#]] &
];

TrBasis4 = DeleteDuplicates[
  canonicalShape /@ TrBasis3
];

Length[TrBasis3]
Length[TrBasis4]


Export[FileNameJoin[{$HomeDirectory, "Downloads", "TrBasis4.txt"}], TrBasis4, "Table"]


(* ::Subsubsection::Closed:: *)
(*Tests generatealtsigned*)


(* ::Text:: *)
(*The "stripOverallPositiveNumericFactor" strips the number that appears after evaluating the indices on G, W,B, sig (anticommutation). So if it has "+2 sign DD[B, ..." The  2 is gone. On the other hand, it leaves the if "-2 sign DD[B, ..." The  -2 stays. The +/- are encoded in "sign".*)


(* generateAlternativeShapesSigned*)

ClearAll[stripOverallPositiveNumericFactor]

(* remove only overall positive numeric factors but keep sign structure intact *)
stripOverallPositiveNumericFactor[expr_] := Which[
  Head[expr] === Times,
    With[{factors = List @@ expr},
      Module[{num, rest},
        num = Times @@ Cases[factors, _?NumericQ];
        rest = DeleteCases[factors, _?NumericQ];
        Which[
          rest === {}, 1,
          NumericQ[num] && num > 0, Times @@ rest,
          True, expr
        ]
      ]
    ],
  NumericQ[expr],
    1,
  True,
    expr
];


stripOverallPositiveNumericFactor[tests2]


(* ::Text:: *)
(*ee*)


ClearAll[normalizeSignedShape]
(* signed cleanup: expand -> simplify sign products -> remove only harmless positive overall numbers -> do NOT call ignoreSigns (as in gen. alt) *)
normalizeSignedShape[expr_] := expr // Expand // simplifySign // stripOverallPositiveNumericFactor;


normalizeSignedShape /@ tests2


ClearAll[generateAlternativeShapesSigned]

generateAlternativeShapesSigned[term_] := Module[{aux},

  aux = {term};

  aux = applyAlternativeShapeRules[aux];

  aux = DeleteDuplicates[Flatten[shuffleDummyIndicesOfType[lor]  /@ aux]];
  aux = DeleteDuplicates[Flatten[shuffleDummyIndicesOfType[col]  /@ aux]];
  aux = DeleteDuplicates[Flatten[shuffleDummyIndicesOfType[iso]  /@ aux]];
  aux = DeleteDuplicates[Flatten[shuffleDummyIndicesOfType[gcol] /@ aux]];
  aux = DeleteDuplicates[Flatten[shuffleDummyIndicesOfType[piso] /@ aux]];
  aux = DeleteDuplicates[Flatten[shuffleDummyIndicesOfType[sp]   /@ aux]];

  aux = normalizeSignedShape /@ aux;
  aux = DeleteDuplicates[aux];

  DeleteDuplicates[Prepend[aux, term]]
];


smallSign = generateAlternativeShapes /@ TrBasis4;
smallCanonSign = First /@ (Sort /@ smallSign);

Length[TrBasis4]
Length[DeleteDuplicates[smallCanonSign]]

TrBasis5 = DeleteDuplicates[smallCanonSign];


Export[FileNameJoin[{$HomeDirectory, "Downloads", "TrBasis5.txt"}], TrBasis5, "Table"]


(* ::Subsection::Closed:: *)
(*Trivial relations [MAIN]  < --- Corrections and explanations*)


(* ::Text:: *)
(*Let's wrap canonicalization and easy zeros and chirality into a single function*)


ClearAll[removeZeroesAndCanonicalize]

removeZeroesAndCanonicalize[expr_] := Block[{base},
  base[1] = expr // canonicalizeDummyIndices // DeleteCases[0];
  base[2] = base[1] // deleteDuplicatesSign;
  base[3] = DeleteCases[Chirality /@ base[2], 0];
  base[4] = base[3] // ApplyTrivial // deleteDuplicatesSign // DeleteCases[0];
  base[4]
]


(* ::Text:: *)
(*So far, the list of initial terms has been reduced a lot. (Maybe even a bit more is still possible). Now:*)
(**)
(*New Trivial Relations MAIN. *)
(**)
(*After wraping the previous functions,  we can reduce whole part of trivial relations to the three functions  //removeZeroesAndCanonicalize*)
(*//generateAlternativeShapes*)
(*//generateAlternativeShapesSigned*)
(*the last two still need to be defined. But it is possible. They contain the index symmetry and antisymmetry identities that were used already, but now, instead of trying to write all the terms in some standard (canonical way), we simply expand each term to get explicitly all the possible ways that one could write it.  A very minimal example of generateAlternativeShapes is provided above*)


firstbasis//removeZeroesAndCanonicalize//showTiming;
lagWithZeroes  = %//Map[generateAlternativeShapes]//Map[Sort]//Map[First]//DeleteDuplicates//showTiming//showLength;
(*lag=%//Map[generateAlternativeShapesSigned]//Map[DeleteDuplicates]//ignoreSigns//Select[DuplicateFreeQ]//Map[First]//showTiming//showLength;*)


lag=lagWithZeroes// removeEasyZeroes //DeleteCases[0] //Map[generateAlternativeShapesSigned] // Map[DeleteDuplicates]//ignoreSigns//Select[DuplicateFreeQ]//Map[First]//showTiming//showLength;


lag //  contractIndices[sp] // readableNotation // MapIndexed[{#2[[1]], #1} &, #] & // Grid


Export[FileNameJoin[{$HomeDirectory, "Downloads", "Final.txt"}], lag, "Table"]


lagSignedCanon1 = First /@ (Sort /@ (generateAlternativeShapesSigned /@ lag));

Length[lag]
Length[DeleteDuplicates[lagSignedCanon1]]


Export[FileNameJoin[{$HomeDirectory, "Downloads", "Final2.txt"}], lagSignedCanon1, "Table"]


(* ::Subsubsection::Closed:: *)
(*Alternative shapes of terms [AUTOMATIC (once generateAlternativeShapes works)]*)


(* ::Text:: *)
(*Functions to 'reshape' the terms fast using dictionaries (replacement rules). First generate all* ways of writing the terms (shapes) *)


(*lagShapesZeroes = Complement[lagWithZeroes,lag]//Map[generateAlternativeShapes]//showTiming//showLength;
lagShapes=lag//Map[generateAlternativeShapesSigned]//showTiming//showLength;*)


(* ::Subsubsection:: *)
(*Reshape terms [AUTOMATIC]*)


(* ::Text:: *)
(*The different shapes are mapped onto the first one, and the rules converted into replacement functions. Then the wrappers "reshapeTerms" are defined, which are used in the rest of the calculation.*)


removeSymAntisymZeroesDict = lagShapesZeroes//Map[getDictionaryOfShapes]//landRulesOnZero//Flatten//rulesToFunction//showTiming;
standardizeShapesDict = lagShapes//Map[getDictionaryOfShapes]//addSigns//Flatten//rulesToFunction//showTiming;

Clear[reshapeTerms,reshapeTermsBare]
reshapeTerms[expr_]:=expr//removeEasyZeroes//removeSymAntisymZeroesDict//DeleteCases[0]//standardizeShapesDict//DeleteCases[0]//deleteDuplicatesSign;
reshapeTermsBare[expr_]:=expr//removeEasyZeroes//removeSymAntisymZeroesDict//DeleteCases[0]//standardizeShapesDict//DeleteCases[0];


res1 = reshapeTerms /@ TrBasis5;
res2 = reshapeTermsBare /@ TrBasis5;

Export[
  FileNameJoin[{$HomeDirectory, "Downloads", "reshapeTerms.txt"}],
  res1,
  "Table"
]

Export[
  FileNameJoin[{$HomeDirectory, "Downloads", "reshapeTermsBare.txt"}],
  res2,
  "Table"
]


Length[reshapeTerms]
Length[reshapeTermsBare]


(* ::Subsection::Closed:: *)
(*SMEFT OPERATORS FIERZ*)


firstbasis // showLength ;


(* ::Subsubsection::Closed:: *)
(*basises*)


salad = Select[
  firstbasis,
  Count[#,GA[g,0][___], 99] >0 &
] // showLength;
saladqL = Select[
  firstbasis,
  Count[#, DD[qL | qLbar, _][___], 99] > 0 &
] // showLength;

saladuR = Select[
  firstbasis,
  Count[#, DD[uR | uRbar, _][___], 99] > 0 &
] // showLength;

saladlL = Select[
  firstbasis,
  Count[#, DD[lL | lLbar, _][___], 99] > 0 &
] // showLength;

saladdR = Select[
  firstbasis,
  Count[#, DD[dR | dRbar, _][___], 99] > 0 &
] // showLength;

saladeR = Select[
  firstbasis,
  Count[#, DD[eR | eRbar, _][___], 99] > 0 &
] // showLength;


(* ::Text:: *)
(*mixed basises*)


saladqLlL = Select[
  firstbasis,
  Count[#, DD[qL | qLbar, _][___], 99] > 0 &&
  Count[#, DD[lL | lLbar, _][___], 99] > 0 &
] // showLength;


saladuRdR = Select[
  firstbasis,
  Count[#, DD[uR | uRbar, _][___], 99] > 0 &&
  Count[#, DD[dR | dRbar, _][___], 99] > 0 &
] // showLength;


saladuReR = Select[
  firstbasis,
  Count[#, DD[uR | uRbar, _][___], 99] > 0 &&
  Count[#, DD[eR | eRbar, _][___], 99] > 0 &
] // showLength;


saladdReR = Select[
  firstbasis,
  Count[#, DD[eR | eRbar, _][___], 99] > 0 &&
  Count[#, DD[dR | dRbar, _][___], 99] > 0 &
] // showLength;


(* ::Subsubsection::Closed:: *)
(*Left chiral fields *)


(* ::Text:: *)
(*qL\[Dash]qL : LL vector-current Fierz*)


ruleFierzVVqL =
  DD[qLbar,0][x1___, sp[a_], x2___] *
  GA[g,0][lor[mu_], sp[a_, b_]] *
  DD[qL,0][y1___, sp[b_], y2___] *

  DD[qLbar,0][z1___, sp[c_], z2___] *
  GA[g,0][lor[mu_], sp[c_, d_]] *
  DD[qL,0][k1___, sp[d_], k2___] :>

  DD[qLbar,0][x1, sp[a], x2] *
  GA[g,0][lor[mu], sp[a, d]] *
  DD[qL,0][k1, sp[d], k2] *

  DD[qLbar,0][z1, sp[c], z2] *
  GA[g,0][lor[mu], sp[c, b]] *
  DD[qL,0][y1, sp[b], y2]


(* ::Text:: *)
(*lL lL  vector vector*)


ruleFierzVVlL =
  DD[lLbar,0][x1___, sp[a_], x2___] *
  GA[g,0][lor[mu_], sp[a_, b_]] *
  DD[lL,0][y1___, sp[b_], y2___] *

  DD[lLbar,0][z1___, sp[c_], z2___] *
  GA[g,0][lor[mu_], sp[c_, d_]] *
  DD[lL,0][k1___, sp[d_], k2___] :>

  DD[lLbar,0][x1, sp[a], x2] *
  GA[g,0][lor[mu], sp[a, d]] *
  DD[lL,0][k1, sp[d], k2] *

  DD[lLbar,0][z1, sp[c], z2] *
  GA[g,0][lor[mu], sp[c, b]] *
  DD[lL,0][y1, sp[b], y2]



ruleFierzVVqLlL =
  DD[qLbar,0][x1___, sp[a_], x2___] *
  GA[g,0][lor[mu_], sp[a_, b_]] *
  DD[qL,0][y1___, sp[b_], y2___] *

  DD[lLbar,0][z1___, sp[c_], z2___] *
  GA[g,0][lor[mu_], sp[c_, d_]] *
  DD[lL,0][k1___, sp[d_], k2___] :>

  DD[qLbar,0][x1, sp[a], x2] *
  GA[g,0][lor[mu], sp[a, d]] *
  DD[lL,0][k1, sp[d], k2] *

  DD[lLbar,0][z1, sp[c], z2] *
  GA[g,0][lor[mu], sp[c, b]] *
  DD[qL,0][y1, sp[b], y2]


getRelationsFromRule[saladqL,ruleFierzVVqL ] //readableNotation ;
getRelationsFromRule[saladlL,ruleFierzVVlL ] //readableNotation ;
getRelationsFromRule[saladqLlL,ruleFierzVVqLlL ] //readableNotation ;


(* ::Subsubsection::Closed:: *)
(*Right Chiral Fields*)


ruleFierzdR =
  DD[dRbar, 0][x1___, sp[a_], x2___] *
  GA[g, 0][lor[mu_], sp[a_, b_]] *
  DD[dR, 0][y1___, sp[b_], y2___] *

  DD[dRbar, 0][z1___, sp[c_], z2___] *
  GA[g, 0][lor[mu_], sp[c_, d_]] *
  DD[dR, 0][k1___, sp[d_], k2___] :>

  -2 *
  DD[dRbar, 0][x1, sp[a], x2] *
  DD[dR, 0][y1, sp[d], y2] *
  DD[dRbar, 0][z1, sp[c], z2] *
  DD[dR, 0][k1, sp[b], k2];

ruleFierzeR =
  DD[eRbar, 0][x1___, sp[a_], x2___] *
  GA[g, 0][lor[mu_], sp[a_, b_]] *
  DD[eR, 0][y1___, sp[b_], y2___] *

  DD[eRbar, 0][z1___, sp[c_], z2___] *
  GA[g, 0][lor[mu_], sp[c_, d_]] *
  DD[eR, 0][k1___, sp[d_], k2___] :>

  -2 *
  DD[eRbar, 0][x1, sp[a], x2] *
  DD[eR, 0][y1, sp[d], y2] *
  DD[eRbar, 0][z1, sp[c], z2] *
  DD[eR, 0][k1, sp[b], k2];

ruleFierzuR =
  DD[uRbar, 0][x1___, sp[a_], x2___] *
  GA[g, 0][lor[mu_], sp[a_, b_]] *
  DD[uR, 0][y1___, sp[b_], y2___] *

  DD[uRbar, 0][z1___, sp[c_], z2___] *
  GA[g, 0][lor[mu_], sp[c_, d_]] *
  DD[uR, 0][k1___, sp[d_], k2___] :>

  -2 *
  DD[uRbar, 0][x1, sp[a], x2] *
  DD[uR, 0][y1, sp[d], y2] *
  DD[uRbar, 0][z1, sp[c], z2] *
  DD[uR, 0][k1, sp[b], k2];
  


(* ::Text:: *)
(*uR - dR*)


ruleFierzVVuRdR =
  DD[uRbar,0][x1___, sp[a_], x2___] *
  GA[g,0][lor[mu_], sp[a_, b_]] *
  DD[uR,0][y1___, sp[b_], y2___] *

  DD[dRbar,0][z1___, sp[c_], z2___] *
  GA[g,0][lor[mu_], sp[c_, d_]] *
  DD[dR,0][k1___, sp[d_], k2___] :>

  DD[uRbar,0][x1, sp[a], x2] *
  GA[g,0][lor[mu], sp[a, d]] *
  DD[dR,0][k1, sp[d], k2] *

  DD[dRbar,0][z1, sp[c], z2] *
  GA[g,0][lor[mu], sp[c, b]] *
  DD[uR,0][y1, sp[b], y2];


(* ::Text:: *)
(*uR - eR*)


ruleFierzVVuReR =
  DD[uRbar,0][x1___, sp[a_], x2___] *
  GA[g,0][lor[mu_], sp[a_, b_]] *
  DD[uR,0][y1___, sp[b_], y2___] *

  DD[eRbar,0][z1___, sp[c_], z2___] *
  GA[g,0][lor[mu_], sp[c_, d_]] *
  DD[eR,0][k1___, sp[d_], k2___] :>

  DD[uRbar,0][x1, sp[a], x2] *
  GA[g,0][lor[mu], sp[a, d]] *
  DD[eR,0][k1, sp[d], k2] *

  DD[eRbar,0][z1, sp[c], z2] *
  GA[g,0][lor[mu], sp[c, b]] *
  DD[uR,0][y1, sp[b], y2];


(* ::Text:: *)
(*dR - eR*)


ruleFierzVVdReR =
  DD[dRbar,0][x1___, sp[a_], x2___] *
  GA[g,0][lor[mu_], sp[a_, b_]] *
  DD[dR,0][y1___, sp[b_], y2___] *

  DD[eRbar,0][z1___, sp[c_], z2___] *
  GA[g,0][lor[mu_], sp[c_, d_]] *
  DD[eR,0][k1___, sp[d_], k2___] :>

  DD[dRbar,0][x1, sp[a], x2] *
  GA[g,0][lor[mu], sp[a, d]] *
  DD[eR,0][k1, sp[d], k2] *

  DD[eRbar,0][z1, sp[c], z2] *
  GA[g,0][lor[mu], sp[c, b]] *
  DD[dR,0][y1, sp[b], y2];


getRelationsFromRule[saladuR, ruleFierzuR]// readableNotation;
getRelationsFromRule[saladdR, ruleFierzdR]// readableNotation;
getRelationsFromRule[saladeR, ruleFierzeR]// readableNotation;



getRelationsFromRule[saladuRdR, ruleFierzVVuRdR] // readableNotation;
getRelationsFromRule[saladuReR, ruleFierzVVuReR]// readableNotation;
getRelationsFromRule[saladdReR, ruleFierzVVdReR]// readableNotation;


(* ::Subsubsection::Closed:: *)
(*Mixed Left Chiral Fields*)


Clear[hasField, mixedBasis, mixedVVSalad];

hasField[expr_, field_] :=
  Count[expr, DD[field, _][___], 99] > 0;

mixedBasis[L_, Lbar_, R_, Rbar_] :=
  Select[
    firstbasis,
    hasField[#, Lbar] &&
    hasField[#, L] &&
    hasField[#, Rbar] &&
    hasField[#, R] &
  ] // showLength;

mixedVVSalad[L_, Lbar_, R_, Rbar_] :=
  Select[
    firstbasis,
    Count[#, GA[g, 0][___], 99] >= 2 &&
    hasField[#, Lbar] &&
    hasField[#, L] &&
    hasField[#, Rbar] &&
    hasField[#, R] &
  ] // showLength;


basisqLuR = mixedBasis[qL, qLbar, uR, uRbar] //  showLength;
basisqLdR = mixedBasis[qL, qLbar, dR, dRbar]//  showLength;
basisqLeR = mixedBasis[qL, qLbar, eR, eRbar]//  showLength;

basislLuR = mixedBasis[lL, lLbar, uR, uRbar]//  showLength;
basislLdR = mixedBasis[lL, lLbar, dR, dRbar]//  showLength;
basislLeR = mixedBasis[lL, lLbar, eR, eRbar]//  showLength;


saladqLuR = mixedVVSalad[qL, qLbar, uR, uRbar]//  showLength;
saladqLdR = mixedVVSalad[qL, qLbar, dR, dRbar]//  showLength;
saladqLeR = mixedVVSalad[qL, qLbar, eR, eRbar]//  showLength;

saladlLuR = mixedVVSalad[lL, lLbar, uR, uRbar]//  showLength;
saladlLdR = mixedVVSalad[lL, lLbar, dR, dRbar]//  showLength;
saladlLeR = mixedVVSalad[lL, lLbar, eR, eRbar]//  showLength;


Clear[makeFierzVLR];

makeFierzVLR[L_, Lbar_, R_, Rbar_] :=
  DD[Lbar, 0][x1___, sp[a_], x2___] *
  GA[g, 0][lor[mu_], sp[a_, b_]] *
  DD[L, 0][y1___, sp[b_], y2___] *

  DD[Rbar, 0][z1___, sp[c_], z2___] *
  GA[g, 0][lor[mu_], sp[c_, d_]] *
  DD[R, 0][w1___, sp[d_], w2___] :>

  -2 *
  DD[Lbar, 0][x1, sp[a], x2] *
  DD[R, 0][w1, sp[d], w2] *
  SD[sp[a, d]] *

  DD[Rbar, 0][z1, sp[c], z2] *
  DD[L, 0][y1, sp[b], y2] *
  SD[sp[c, b]];


ruleFierzqLuR = makeFierzVLR[qL, qLbar, uR, uRbar];
ruleFierzqLdR = makeFierzVLR[qL, qLbar, dR, dRbar];
ruleFierzqLeR = makeFierzVLR[qL, qLbar, eR, eRbar];

ruleFierzlLuR = makeFierzVLR[lL, lLbar, uR, uRbar];
ruleFierzlLdR = makeFierzVLR[lL, lLbar, dR, dRbar];
ruleFierzlLeR = makeFierzVLR[lL, lLbar, eR, eRbar];

checkRule[ruleFierzqLuR];
checkRule[ruleFierzqLdR];
checkRule[ruleFierzqLeR];

checkRule[ruleFierzlLuR];
checkRule[ruleFierzlLdR];
checkRule[ruleFierzlLeR];


relFierzqLuR = getRelationsFromRule[basisqLuR, ruleFierzqLuR] // readableNotation;
relFierzqLdR = getRelationsFromRule[basisqLdR, ruleFierzqLdR] // readableNotation;
relFierzqLeR = getRelationsFromRule[basisqLeR, ruleFierzqLeR] // readableNotation;

relFierzlLuR = getRelationsFromRule[basislLuR, ruleFierzlLuR] // readableNotation;
relFierzlLdR = getRelationsFromRule[basislLdR, ruleFierzlLdR] // readableNotation;
relFierzlLeR = getRelationsFromRule[basislLeR, ruleFierzlLeR] // readableNotation;


(* ::Subsection::Closed:: *)
(*dirac *)


(* ::Text:: *)
(*put labels and match in note book later*)


ruleGA1 =
  GA[g,0][lor[mu_], sp[a_,b_]] *
  GA[g,0][lor[mu_], sp[b_,c_]] :>
  4 * SD[sp[a,c]];
ga1 = getRelationsFromRule[salad, ruleGA1]


ruleGA1 =
  GA[g,0][lor[mu_], sp[a_,b_]] *
  GA[g,0][lor[mu_], sp[b_,c_]] :>
  4 * SD[sp[a,c]];
ga1 = getRelationsFromRule[salad, ruleGA1]


?SD[]


ruleGA2 =
  GA[g,0][lor[mu_], sp[a_,b_]] *
  GA[g,0][lor[nu_], sp[a_,b_]]  :>
  KroneckerDelta[lor[mu], lor[nu]] * SD[sp[a,b]]-  (*MT doesnt exist?*)
  I * SIG[lor[mu,nu], sp[a,b]];
ga2 = getRelationsFromRule[salad, ruleGA2]


ruleSIG1 =
  (
    GA[g,0][lor[mu_], sp[a_, b_]] *
    GA[g,0][lor[nu_], sp[b_, c_]]
    -
    GA[g,0][lor[nu_], sp[a_, b_]] *
    GA[g,0][lor[mu_], sp[b_, c_]]
  ) :>
  (2/I) * GA[sig,0][lor[mu, nu], sp[a, c]];
sig1 = getRelationsFromRule[salad, ruleSIG1]
(*try to flip sides to see if can find relation*)


ruleSIG1 =
  GA[g, 0][lor[mu_], sp[a_, b_]] *
  GA[g, 0][lor[nu_], sp[b_, c_]] :>
   GA[g, 0][lor[nu], sp[a, b]] *
   GA[g, 0][lor[mu], sp[b, c]]
   + (2/I) * GA[sig, 0][lor[mu, nu], sp[a, c]];

checkRule[ruleSIG1];

sig1 = getRelationsFromRule[salad, ruleSIG1] // readableNotation;


ruleGA3 =
  GA[g, 0][lor[mu1_], sp[a_, b_]] *
  GA[g, 0][lor[nu_], sp[b_, c_]] *
  GA[g, 0][lor[mu2_], sp[c_, d_]] /; mu1 === mu2 :>
   -2 GA[g, 0][lor[nu], sp[a, d]];

ruleGA4 =
  GA[g, 0][lor[mu1_], sp[a_, b_]] *
  GA[g, 0][lor[nu_], sp[b_, c_]] *
  GA[g, 0][lor[rho_], sp[c_, d_]] *
  GA[g, 0][lor[mu2_], sp[d_, e_]] /; mu1 === mu2 :>
   4 KroneckerDelta[lor[nu], lor[rho]] * SD[sp[a, e]];

checkRule[ruleGA3];
checkRule[ruleGA4];


saladGA3 = Select[
  firstbasis,
  Count[#, GA[g, 0][___], 99] >= 3 &
] // showLength;

saladGA4 = Select[
  firstbasis,
  Count[#, GA[g, 0][___], 99] >= 4 &
] // showLength;

relGA3 = getRelationsFromRule[saladGA3, ruleGA3] // readableNotation;
relGA4 = getRelationsFromRule[saladGA4, ruleGA4] // readableNotation;


ruleGA3 =
  GA[g,0][lor[mu_], sp[a_, b_]]*
  GA[g,0][lor[nu_], sp[b_, c_]]*
  GA[g,0][lor[mu_], sp[c_, d_]]  :>
   -2 GA[g,0][lor[nu], sp[a, d]];

checkRule[ruleGA3];
 getRelationsFromRule[salad, ruleGA3] //readableNotation;


ruleGA4 =
  GA[g,0][lor[mu_], sp[a_,b_]] *
  GA[g,0][lor[nu_], sp[b_,c_]] *
  GA[g,0][lor[rho_], sp[c_,d_]] *
  GA[g,0][lor[mu_], sp[d_,e_]]  :>
  4 * KroneckerDelta[lor[nu], lor[rho]] * SD[sp[a,e]];
ga4 = getRelationsFromRule[salad, ruleGA4]
(*MT doesnt exist?*)


(* ::Subsubsection:: *)
(**)


(* ::Text:: *)
(**)


(* ::Subsection::Closed:: *)
(*Schouten(Dont run)*)


(*DownValues[schoutenCandidateQ]*)


(*Tally[nDistinctLorentz /@ firstbasis] // SortBy[#, First] &*)


(*Max[nDistinctLorentz /@ firstbasis]*)


(* ::Subsection::Closed:: *)
(*Schouten-only Lorentz-projected basis*)


BBsave = BB;

(* Do not start with Range[10]. 
   First try maxBlocksSCH = 8. If this works, you can later try 9. *)
maxBlocksSCH = 8;

(* 
   Targeted Schouten building blocks.
   Internal indices are removed from the beginning.
   We explicitly include G, W, B here even if they are commented out in the main BB.
*)
BBsch = {
  G    iSpin^0 iLor^2 iCol^0 iIso^0 iGCol^0 iPIso^0 dim^2 gtSU3^0 gtSU2L^0 gtU1Y^0,
  W    iSpin^0 iLor^2 iCol^0 iIso^0 iGCol^0 iPIso^0 dim^2 gtSU3^0 gtSU2L^0 gtU1Y^0,
  B    iSpin^0 iLor^2 iCol^0 iIso^0 iGCol^0 iPIso^0 dim^2 gtSU3^0 gtSU2L^0 gtU1Y^0,

  H    iSpin^0 iLor^0 iCol^0 iIso^0 iGCol^0 iPIso^0 dim^1 gtSU3^0 gtSU2L^2  gtU1Y^(1/2),
  Hc   iSpin^0 iLor^0 iCol^0 iIso^0 iGCol^0 iPIso^0 dim^1 gtSU3^0 gtSU2L^(-2) gtU1Y^(-1/2),

  der  iSpin^0 iLor^1 iCol^0 iIso^0 iGCol^0 iPIso^0 dim^1 gtSU3^0 gtSU2L^0 gtU1Y^0
};

BB = BBsch;

ClearAll[nIndicesLor, inCurrentBBQ];

inCurrentBBQ[field_] :=
  Cases[BB, x_ /; ! FreeQ[x, field]] =!= {};

nIndicesLor[field_] := nIndicesLor[field] = Module[{hit},
  hit = Cases[BB, x_ /; ! FreeQ[x, field]];

  If[hit === {},
    Print["Missing from current BB: ", field];
    0,
    Exponent[First[hit], iLor]
  ]
];

(* Only apply derivatives to fields that are actually present in BBsch. *)
derivativeFieldsSCH =
  Select[
    {G, W, B, H, Hc},
    inCurrentBBQ[#] &
  ];

combSCH =
  getCombinations[BB, Range[3, maxBlocksSCH]] // Flatten;

maxLorSlotsSCH =
  If[combSCH === {},
    0,
    Max[Exponent[#, iLor] & /@ combSCH]
  ];

lorentzSlotDistributionSCH =
  SortBy[
    Tally[Exponent[#, iLor] & /@ combSCH],
    First
  ];

Print["Length[combSCH] = ", Length[combSCH]];
Print["Max Lorentz slots before index insertion = ", maxLorSlotsSCH];
Print["Lorentz-slot distribution before index insertion = ", lorentzSlotDistributionSCH];

(* 
   Select only combinations that can possibly contain a Schouten structure.
   Schouten needs at least 5 Lorentz indices.
*)
selectedSCH =
  Select[
    combSCH,
    Exponent[#, iLor] >= 5 &&
    EvenQ[Exponent[#, iLor]] &&
    Exponent[#, dim] == ORDER &&
    FreeQ[#, gtSU3 | gtSU2L | gtU1Y] &
  ];

Print["Length[selectedSCH] = ", Length[selectedSCH]];

If[selectedSCH === {},

  (
    Print["No Schouten candidates found at this stage. Try maxBlocksSCH = 9, or relax the dimension condition for testing."];
    firstbasisSCH = {};
  ),

  (
    BcSCH =
      selectedSCH /. {
        iSpin -> 1,
        iLor -> 1,
        iCol -> 1,
        iIso -> 1,
        iGCol -> 1,
        iPIso -> 1,
        dim -> 1
      } //
      DeleteCases[der^_] //
      DeleteDuplicates;

    tmpSCH =
      BcSCH /. {
        g -> GA[g],
        g5 -> GA[g5],
        sig -> GA[sig],
        Gll -> GA[Gll],
        Pll -> GA[Pll]
      };

    tmpSCH =
      tmpSCH //
      applyDerivativesOn[derivativeFieldsSCH];

    tmpSCH =
      tmpSCH //
      insertIndexPlaceHoldersAddDerivatives[nIndicesLor][DD, GA];

    tmpSCH =
      tmpSCH /. index[n_] :> lor[index[n]];

    tmpSCH =
      tmpSCH //
      insertIndicesOfType[{j1, j2, j3, j4, j5, j6, j7, j8, j9, j10}];

    firstbasisSCH =
      tmpSCH /. A_[a___, lor[], b___] :> A[a, b];

    Print["Length[firstbasisSCH] = ", Length[firstbasisSCH]];
  )
];

BB = BBsave;


ClearAll[
  lorentzIndexSlots,
  nLorentzSlots,
  lorentzIndexLabels,
  nDistinctLorentzLabels,
  schoutenCandidateQ
];

lorentzIndexSlots[expr_] :=
  Flatten @ Cases[
    expr,
    lor[x___] :> {x},
    Infinity
  ];

nLorentzSlots[expr_] :=
  Length[lorentzIndexSlots[expr]];

lorentzIndexLabels[expr_] :=
  DeleteDuplicates[lorentzIndexSlots[expr]];

nDistinctLorentzLabels[expr_] :=
  Length[lorentzIndexLabels[expr]];

schoutenCandidateQ[expr_] :=
  nLorentzSlots[expr] >= 5;

{
  "Length[firstbasisSCH]" -> Length[firstbasisSCH],
  "Max Lorentz slots" -> If[firstbasisSCH === {}, 0, Max[nLorentzSlots /@ firstbasisSCH]],
  "Lorentz-slot distribution" -> If[firstbasisSCH === {}, {}, SortBy[Tally[nLorentzSlots /@ firstbasisSCH], First]],
  "Max distinct Lorentz labels" -> If[firstbasisSCH === {}, 0, Max[nDistinctLorentzLabels /@ firstbasisSCH]],
  "Distinct-label distribution" -> If[firstbasisSCH === {}, {}, SortBy[Tally[nDistinctLorentzLabels /@ firstbasisSCH], First]]
}


ClearAll[schoutenCandidateQ];

schoutenCandidateQ[expr_] :=
  nDistinctLorentzLabels[expr] >= 5;
  
saladSCH =
  Select[
    firstbasisSCH,
    schoutenCandidateQ[#] &
  ] // showLength;


relSCH =
  getSchoutenJ /@ saladSCH //
  Flatten //
  reshapeTerms //
  identifyTerms //
  deleteDuplicatesSign //
  showLength //
  showTiming;


 


(* ::Subsection::Closed:: *)
(*EOM Fermions*)


(* ::Subsubsection::Closed:: *)
(*normal fermion eom*)


Clear[
  ruleEOMqL, ruleEOMlL, ruleEOMuR, ruleEOMdR, ruleEOMeR,
  ruleEOMqLbar, ruleEOMlLbar, ruleEOMuRbar, ruleEOMdRbar, ruleEOMeRbar
];

ruleEOMqL =
  DD[qL, 1][lor[mu_], sp[sp1_], col[col1_], iso[iso1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    -ii * (
      Yu * DD[Hc, 0][iso[iso1]] * DD[uR, 0][sp[sp2], col[col1]]
      +
      Yd * DD[H, 0][iso[iso1]] * DD[dR, 0][sp[sp2], col[col1]]
    );

ruleEOMlL =
  DD[lL, 1][lor[mu_], sp[sp1_], iso[iso1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    -ii * Ye *
      DD[H, 0][iso[iso1]] *
      DD[eR, 0][sp[sp2]];

ruleEOMuR =
  DD[uR, 1][lor[mu_], sp[sp1_], col[col1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    -ii * Yudag *
      DD[H, 0][iso[iEOM]] *
      DD[qL, 0][sp[sp2], col[col1], iso[iEOM]];

ruleEOMdR =
  DD[dR, 1][lor[mu_], sp[sp1_], col[col1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    -ii * Yddag *
      DD[Hc, 0][iso[iEOM]] *
      DD[qL, 0][sp[sp2], col[col1], iso[iEOM]];

ruleEOMeR =
  DD[eR, 1][lor[mu_], sp[sp1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    -ii * Yedag *
      DD[Hc, 0][iso[iEOM]] *
      DD[lL, 0][sp[sp2], iso[iEOM]];


(* ::Subsubsection::Closed:: *)
(*bared fermions*)


ruleEOMqLbar =
  DD[qLbar, 1][lor[mu_], sp[sp2_], col[col1_], iso[iso1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    ii * (
      Yudag * DD[uRbar, 0][sp[sp1], col[col1]] * DD[H, 0][iso[iso1]]
      +
      Yddag * DD[dRbar, 0][sp[sp1], col[col1]] * DD[Hc, 0][iso[iso1]]
    );

ruleEOMlLbar =
  DD[lLbar, 1][lor[mu_], sp[sp2_], iso[iso1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    ii * Yedag *
      DD[eRbar, 0][sp[sp1]] *
      DD[Hc, 0][iso[iso1]];

ruleEOMuRbar =
  DD[uRbar, 1][lor[mu_], sp[sp2_], col[col1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    ii * Yu *
      DD[qLbar, 0][sp[sp1], col[col1], iso[iEOM]] *
      DD[Hc, 0][iso[iEOM]];

ruleEOMdRbar =
  DD[dRbar, 1][lor[mu_], sp[sp2_], col[col1_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    ii * Yd *
      DD[qLbar, 0][sp[sp1], col[col1], iso[iEOM]] *
      DD[H, 0][iso[iEOM]];

ruleEOMeRbar =
  DD[eRbar, 1][lor[mu_], sp[sp2_]] *
  GA[g, 0][lor[mu_], sp[sp1_, sp2_]] :>
    ii * Ye *
      DD[lLbar, 0][sp[sp1], iso[iEOM]] *
      DD[H, 0][iso[iEOM]];


(* ::Subsubsection::Closed:: *)
(*results*)


ruleEOMFermions = {
  ruleEOMqL,
  ruleEOMlL,
  ruleEOMuR,
  ruleEOMdR,
  ruleEOMeR,
  ruleEOMqLbar,
  ruleEOMlLbar,
  ruleEOMuRbar,
  ruleEOMdRbar,
  ruleEOMeRbar
};


saladEOMFermions =
  Select[
    firstbasis,
    Count[
      #,
      DD[
        qL | lL | uR | dR | eR | qLbar | lLbar | uRbar | dRbar | eRbar,
        1
      ][___],
      99
    ] > 0
    &&
    Count[#, GA[g, 0][___], 99] > 0 &
  ] // showLength;


Clear[i1, i2, i3, i4, i5, i6];
Clear[j1, j2, j3, j4, j5, j6];
Clear[s1, s2, s3, s4, s5, s6];
Clear[c1, c2, c3, c4, c5, c6];


relEOMFermions =
  Flatten[
    getRelationsFromRule[saladEOMFermions, #] & /@ ruleEOMFermions
  ];
(* // reshapeTerms
  // identifyTerms
  // deleteDuplicatesSign
  // showLength;*)


(* ::Subsection::Closed:: *)
(*EOM Field Strengths*)


Clear[
  gY, gS, gW,
  currentB, currentG, currentW,
  ruleEOMB, ruleEOMG, ruleEOMW,
  ruleEOMGauge
];

Clear[
  mu, rho, rho1, rho2,
  sBq1, sBq2, sBl1, sBl2, sBu1, sBu2, sBd1, sBd2, sBe1, sBe2,
  cBq, cBu, cBd,
  iBq, iBl, iBH,
  sGq1, sGq2, sGu1, sGu2, sGd1, sGd2,
  cGq1, cGq2, cGu1, cGu2, cGd1, cGd2,
  iGq,
  sWq1, sWq2, sWl1, sWl2,
  cWq,
  iWq1, iWq2, iWl1, iWl2, iWH1, iWH2
];


(* ::Subsubsection::Closed:: *)
(*G*)


Clear[currentG, ruleEOMG, gS];

currentG[mu_, adj_] :=
  gS * (
    DD[qLbar, 0][sp[sGq1], col[cGq1], iso[iGq]] *
      GA[g, 0][lor[mu], sp[sGq1, sGq2]] *
      DD[Gll, 0][col[cGq1, cGq2], gcol[adj]] *
      DD[qL, 0][sp[sGq2], col[cGq2], iso[iGq]]

    +

    DD[uRbar, 0][sp[sGu1], col[cGu1]] *
      GA[g, 0][lor[mu], sp[sGu1, sGu2]] *
      DD[Gll, 0][col[cGu1, cGu2], gcol[adj]] *
      DD[uR, 0][sp[sGu2], col[cGu2]]

    +

    DD[dRbar, 0][sp[sGd1], col[cGd1]] *
      GA[g, 0][lor[mu], sp[sGd1, sGd2]] *
      DD[Gll, 0][col[cGd1, cGd2], gcol[adj]] *
      DD[dR, 0][sp[sGd2], col[cGd2]]
  );


ruleEOMG = {
  (
    DD[G, 1][lor[rho1_, rho2_, mu_], gcol[adj_]] /; rho1 === rho2
  ) :>
    currentG[mu, adj],

  (
    DD[G, 1][lor[rho1_, mu_, rho2_], gcol[adj_]] /; rho1 === rho2
  ) :>
    -currentG[mu, adj]
};


saladEOMG =
  Select[
    firstbasis,
    Count[#, DD[G, 1][___], {0, Infinity}] > 0 &
  ] // showLength;

relEOMG =
  Flatten[
    getRelationsFromRule[saladEOMG, #] & /@ ruleEOMG
  ];

relEOMG // readableNotation


(* ::Subsubsection::Closed:: *)
(*B*)


currentB[mu_] :=
  gY * (
    (1/2) * ii * (
      DD[Hc, 0][iso[iBH]] *
        DD[H, 1][lor[mu], iso[iBH]]
      -
      DD[Hc, 1][lor[mu], iso[iBH]] *
        DD[H, 0][iso[iBH]]
    )

    + (1/6) *
      DD[qLbar, 0][sp[sBq1], col[cBq], iso[iBq]] *
      GA[g, 0][lor[mu], sp[sBq1, sBq2]] *
      DD[qL, 0][sp[sBq2], col[cBq], iso[iBq]]

    - (1/2) *
      DD[lLbar, 0][sp[sBl1], iso[iBl]] *
      GA[g, 0][lor[mu], sp[sBl1, sBl2]] *
      DD[lL, 0][sp[sBl2], iso[iBl]]

    + (2/3) *
      DD[uRbar, 0][sp[sBu1], col[cBu]] *
      GA[g, 0][lor[mu], sp[sBu1, sBu2]] *
      DD[uR, 0][sp[sBu2], col[cBu]]

    - (1/3) *
      DD[dRbar, 0][sp[sBd1], col[cBd]] *
      GA[g, 0][lor[mu], sp[sBd1, sBd2]] *
      DD[dR, 0][sp[sBd2], col[cBd]]

    - 
      DD[eRbar, 0][sp[sBe1]] *
      GA[g, 0][lor[mu], sp[sBe1, sBe2]] *
      DD[eR, 0][sp[sBe2]]
  );


ruleEOMB = {
  (
    DD[B, 1][lor[rho1_, rho2_, mu_]] /; rho1 === rho2
  ) :>
    currentB[mu],

  (
    DD[B, 1][lor[rho1_, mu_, rho2_]] /; rho1 === rho2
  ) :>
    -currentB[mu]
};


saladEOMB =
  Select[
    firstbasis,
    Count[#, DD[B, 1][___], {0, Infinity}] > 0 &
  ] // showLength;


relEOMB =
  Flatten[
    getRelationsFromRule[saladEOMB, #] & /@ ruleEOMB
  ];

relEOMB // readableNotation


(* ::Subsubsection::Closed:: *)
(*W*)


(* ::Text:: *)
(*current*)


Clear[currentW, ruleEOMW, gW];

currentW[mu_, adj_] :=
  (gW/2) * (
    ii * (
      DD[Hc, 0][iso[iWH1]] *
        DD[Pll, 0][iso[iWH1, iWH2], piso[adj]] *
        DD[H, 1][lor[mu], iso[iWH2]]

      -

      DD[Hc, 1][lor[mu], iso[iWH1]] *
        DD[Pll, 0][iso[iWH1, iWH2], piso[adj]] *
        DD[H, 0][iso[iWH2]]
    )

    +

    DD[qLbar, 0][sp[sWq1], col[cWq], iso[iWq1]] *
      GA[g, 0][lor[mu], sp[sWq1, sWq2]] *
      DD[Pll, 0][iso[iWq1, iWq2], piso[adj]] *
      DD[qL, 0][sp[sWq2], col[cWq], iso[iWq2]]

    +

    DD[lLbar, 0][sp[sWl1], iso[iWl1]] *
      GA[g, 0][lor[mu], sp[sWl1, sWl2]] *
      DD[Pll, 0][iso[iWl1, iWl2], piso[adj]] *
      DD[lL, 0][sp[sWl2], iso[iWl2]]
  );


(* ::Text:: *)
(*rule*)


ruleEOMW = {
  (
    DD[W, 1][lor[rho1_, rho2_, mu_], piso[adj_]] /; rho1 === rho2
  ) :>
    currentW[mu, adj],

  (
    DD[W, 1][lor[rho1_, mu_, rho2_], piso[adj_]] /; rho1 === rho2
  ) :>
    -currentW[mu, adj]
};


saladEOMW =
  Select[
    firstbasis,
    Count[#, DD[W, 1][___], {0, Infinity}] > 0 &
  ] // showLength;

relEOMW =
  Flatten[
    getRelationsFromRule[saladEOMW, #] & /@ ruleEOMW
  ];

relEOMW // readableNotation


(* ::Subsection::Closed:: *)
(*bianchi*)


ClearAll[ruleBianchiB, ruleBianchiW, ruleBianchiG];

ruleBianchiB =
  DD[B, 1][pre___, lor[a_, b_, c_], post___] :>
    (
      -DD[B, 1][pre, lor[b, c, a], post]
      -DD[B, 1][pre, lor[c, a, b], post]
    );

ruleBianchiW =
  DD[W, 1][pre___, lor[a_, b_, c_], post___] :>
    (
      -DD[W, 1][pre, lor[b, c, a], post]
      -DD[W, 1][pre, lor[c, a, b], post]
    );

ruleBianchiG =
  DD[G, 1][pre___, lor[a_, b_, c_], post___] :>
    (
      -DD[G, 1][pre, lor[b, c, a], post]
      -DD[G, 1][pre, lor[c, a, b], post]
    );


checkRule[ruleBianchiB];
checkRule[ruleBianchiW];
checkRule[ruleBianchiG];


lagBianchi =
  Select[
    firstbasis,
    Count[#, DD[B | W | G, 1][___], Infinity] > 0 &
  ] // showLength;


DD[B, 1][lor[a, b, c]] /. ruleBianchiB


lagBianchiB =
  Select[
    firstbasis,
    Count[#, DD[B, 1][___], Infinity] > 0 &
  ] // showLength;

lagBianchiW =
  Select[
    firstbasis,
    Count[#, DD[W, 1][___], Infinity] > 0 &
  ] // showLength;

lagBianchiG =
  Select[
    firstbasis,
    Count[#, DD[G, 1][___], Infinity] > 0 &
  ] // showLength;


relBianchiB =
  getRelationsFromRule[lagBianchiB, ruleBianchiB] //
  reshapeTerms //
  identifyTerms //
  deleteDuplicatesSign //
  showLength //
  showTiming;
relBianchiW =
  getRelationsFromRule[lagBianchiW, ruleBianchiW] //
  reshapeTerms //
  identifyTerms //
  deleteDuplicatesSign //
  showLength //
  showTiming;
relBianchiG =
  getRelationsFromRule[lagBianchiG, ruleBianchiG] //
  reshapeTerms //
  identifyTerms //
  deleteDuplicatesSign //
  showLength //
  showTiming;


(* ::Subsection:: *)
(*Covariant Derivative Communication*)


(* ::Subsubsection:: *)
(*qL only G field*)


Cases[
  firstbasis,
  DD[qL, 2][___],
  {0, Infinity}
] // DeleteDuplicates // Take[#, UpTo[20]] &


Clear[ruleCOMqLG, gS];

ruleCOMqLG =
  DD[qL, 2][lor[mu_, nu_], sp[sp1_], col[col1_], iso[iso1_]] /; mu =!= nu :>
    DD[qL, 2][lor[nu, mu], sp[sp1], col[col1], iso[iso1]]
    - ii * gS *
      DD[G, 0][lor[mu, nu], gcol[Acom]] *
      DD[Gll, 0][col[col1, col2com], gcol[Acom]] *
      DD[qL, 0][sp[sp1], col[col2com], iso[iso1]];


saladCOMqLG =
  Select[
    firstbasis,
    Count[#, DD[qL, 2][___], {0, Infinity}] > 0 &
  ] // showLength;


relCOMqLG =
  getRelationsFromRule[saladCOMqLG, ruleCOMqLG];

relCOMqLG // readableNotation


(* ::Subsection::Closed:: *)
(*Reorder operators*)


(* ::Subsubsection::Closed:: *)
(*Symmetrize on H and C*)


(* ::Text:: *)
(*Define discrete transformations.*)
(*Find linear combinations of terms that are even under H and eigenvectors of C.*)
(*Define transformation from the symmetric to the raw operator basis. *)


Clear[applyC,applyH]
applyC[terms_]:=terms/.DD[fp,n_][i___]:>sign DD[fp,n][i]//reverseTR//pullSign//addSigns//reshapeTermsBare
applyH[terms_]:=terms/.DD[chim,n_][i___]:>sign DD[chim,n][i]//simpleConjugate//reverseTR//pullSign//addSigns//simplifySign//reshapeTermsBare

lag//showLength//symmetrize[applyH,applyC]//showTiming//showLength;
symToRawOpes=%//identifyTerms//getTransformationRules//showTiming//showLength;
{opesCE,opesCO}=separateEvenOddUnder[applyC][symToRawOpes,lag]//showTiming;


rawToSymOpes=symToRawOpes//getInverseTransformation//showTiming;


(* ::Subsubsection::Closed:: *)
(*Define preferred terms*)


(* ::Text:: *)
(*Define the preferential terms for the final minimal basis.*)


Clear[scorePreferredOperators]
scorePreferredOperators[term_]:=
hasNotHas[term,u,chim|chip|fm|fp]             * 1 +
hasNotHas[term,chim|chip,fm|fp]               * 10^-1 + 
hasNotHas[term,fm|fp,chim|chip]                * 10^-2 + 
hasField[term,fm|fp]*hasField[term,chim|chip] * 10^-3 + (*irrelevant*)
nTraces[term]                   * 10^-4 +
(10 - nFields[term,chim|chip])  * 10^-6 +
(10 - nFields[term,fm|fp])      * 10^-7 +
(10 - nFields[term,u])          * 10^-8 +
nDer[term]               * 10^-9 +
nSeqDer[term]            * 10^-10


lag//reorderOperators[scorePreferredOperators]//identifyTerms;
symToPrefOpes = %//moveUp[opesCE]//getTransformationRulesFromListOrder;
prefToSymOpes = symToPrefOpes//getInverseTransformationNaive;


(* ::Subsubsection::Closed:: *)
(*Convert to functions [import]*)


(* ::Text:: *)
(*Convert rules to functions*)


symToRawOpesF = symToRawOpes // rulesToFunction;
rawToSymOpesF = rawToSymOpes // rulesToFunction;

symToPrefOpesF = symToPrefOpes // rulesToFunction;
prefToSymOpesF = prefToSymOpes // rulesToFunction;


(* ::Subsection::Closed:: *)
(*Reduce to minimal basis*)


(* ::Text:: *)
(*Now we put together all the previous results of the calculation to do the reduction to a minimal basis.*)
(*First we transform the relations (in the raw basis) into the proper orderings (pref basis). Optionally, remove C odd operators to speed up. And build a relation matrix with the operator relations. *)
(*Gaussian Elimination is performed. In particular the relation matrix is decomposed into a unitary (Q) and an upper triangular (R)  matrix with getMinimalBasis, which uses the third-party code SuiteSparseQR, written in C++.*)
(*The transformations are undone to be able to read the terms of the final basis.*)
(**)


{relTD,relFMU,relEOM,relBIC,relCOM,relCH[Nf],relSCH} /. Nf->8;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix //EchoFunction[MatrixPlot] // showTiming;
miniBasisNfGen = relationMatrix // correctDim[Length[opesCE]] // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;


{relTD,relFMU,relEOM,relBIC,relCOM,relCH[Nf],relSCH} /. Nf->2;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix //EchoFunction[MatrixPlot] // showTiming;
miniBasisNf2 = relationMatrix // correctDim[Length[opesCE]] // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;


{relTD,relFMU,relEOM,relBIC,relCOM,relCH[Nf],relSCH} /. Nf->3;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix //EchoFunction[MatrixPlot] // showTiming;
miniBasisNf3 = relationMatrix // correctDim[Length[opesCE]] // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;


miniBasisNfGen = summary[miniBasis, {Identity}, 
1->1,
(chip | chim ):>0,
(chip | chim | fp | fm):>0
] ;


Now-START


(* ::Subsection::Closed:: *)
(*Save results*)


DumpSave[NotebookDirectory[]<>"/save/EvenIP_P6_SAFENAME.mx",
{relTD,relFMU,relEOM,relBIC,relCOM,relCH,relSCH,
lag, lagShapes, lagShapesZeroes, opesCE, opesCO,
rawToSymOpes, symToPrefOpes, prefToSymOpes, symToRawOpes, rawOpesToTerms,
miniBasisNfGen,miniBasisNf3,miniBasisNf2,
possibleTerms
}];
