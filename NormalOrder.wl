(* ::Package:: *)

(*Wolfram Language Package*)
(*NormalOrder package for calculate normal order for fermionic operator.*)

BeginPackage["NormalOrder`"] 


FermionNormalOrder::usage = "FermionNoramlOrder[a] calculate normal order for fermionic operator."
c::usage = "Fermionic Operator"
d::usage = "Creation operators"
o::usage = "Annihilation operators"



Begin["`Private`"]

(*Calculate normal order for 'pure' fermionic operator term.*)
norderF[]:=1;
(*Commutation relation:[c(k1),c\[Dagger](k2)]=\[Delta](k1,k2)*)
norderF[left___,c[o,k1__],c[d,k2__],right___]:=-norderF[left,c[d,k2],c[o,k1],right]+Times@@MapThread[KroneckerDelta,{{k1},{k2}}]norderF[left,right];
(*Commutation relations:[c(k1),c(k2)]=[c\[Dagger](k1),c\[Dagger](k2)]=0*)
norderF[left___,c[o,k1__],c[o,k2__],right___]/;!OrderedQ[{{k1},{k2}}]:=-norderF[left,c[o,k2],c[o,k1],right];
norderF[left___,c[d,k1__],c[d,k2__],right___]/;!OrderedQ[{{k1},{k2}}]:=-norderF[left,c[d,k2],c[d,k1],right];
(*Fermion Creatiom/annihilation :c(k1)c(k1)= c\[Dagger](k1)c\[Dagger](k1) =0*)
norderF[left___,c[o,k1__],c[o,k2__],right___]/;SameQ[k1,k2]:= 0;
norderF[left___,c[d,k1__],c[d,k2__],right___]/;SameQ[k1,k2]:= 0;

(*Expand NonCommutativeMultiply make it satisfy distributivity.*)
ExpandFerOp[(h:Plus)[a__]]:=Total[ExpandFerOp/@{a}]
ExpandFerOp[(h:NonCommutativeMultiply)[a___,b_Plus,c___]]:=Distribute[h[a,b,c],Plus,h,Plus,ExpandFerOp[h[##]]&]
(*Replace normal multiply*)
ExpandFerOp[(h:Times)[a__]] := ExpandFerOp[NonCommutativeMultiply[a]]
ExpandFerOp[(h:NonCommutativeMultiply)[a___,b_Times,c___]]:=ExpandFerOp[h[a,Most[b],Last[b],c]]
ExpandFerOp[a_]:=GetFermionicTerm[a]

(*Extracting normal multiply fator.*)
GetFermionicTerm[a_] :=a
GetFermionicTerm[(h:NonCommutativeMultiply)[a__]] :=Times@@Select[{a},!MatchQ[#,c[_,_]]&]norderF@@Select[{a},MatchQ[#,c[_,_]]&]

(*Get human readability result.*)
GetNorderFList[]:=1
GetNorderFList[(h:Times)[a___]]:= Times@@Select[{a},!MatchQ[#,norderF[___]]&] GetNorderFList@@Select[{a},MatchQ[#,norderF[___]]&]
GetNorderFList[(h:norderF)[a__]] /;(Length[{a}]>1):=NonCommutativeMultiply[a]
GetNorderFList[(h:norderF)[a__]] /;(Length[{a}]==1):=a
GetNorderFList[a_]/;!MatchQ[a,norderF[__]] :=a
GetResult[(h:Plus)[a__]]:=Total[GetNorderFList/@{a}]
GetResult[a_]:=GetNorderFList[a]


FermionNormalOrder[a_]:=GetResult[ExpandFerOp[a//ExpandAll]//ExpandAll]

End[]

EndPackage[]
