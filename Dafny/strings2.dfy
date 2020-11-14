predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || pre != str[..|pre|]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}


predicate isSubstringPred(sub:string, str:string)
{
  (|sub| <= |str|) && (exists i :: 0 <= i < |str| && isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	forall i :: 0 <= i < |str| ==> isNotPrefixPred(sub, str[i..])
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	k <= |str1| && k <= |str2| && exists i :: 0 <= i <= |str1|-k && isSubstringPred(str1[i..][..k], str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	k > |str1| || k > |str2| || forall i :: 0 <= i <= |str1|-k ==> isNotSubstringPred(str1[i..][..k], str2)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}