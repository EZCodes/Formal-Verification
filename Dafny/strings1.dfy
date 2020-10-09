predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| > |str|
    {return false;}

  var i := 0;
  while i < |pre|
    decreases |pre| - i
    invariant 0 <= i <= |pre|
    invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
  {
    if pre[i] != str[i]
    {
        return false;
    } 
    i := i + 1;
  }
 return true;
}

predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..])
}

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
    if |sub| > |str| {
        return false;
    }

    var i := |str| - |sub|;
    while i >= 0 
    decreases i
    invariant i >= -1
    invariant forall j :: i <  j <= |str|-|sub| ==> !(isPrefixPredicate(sub, str[j..]))
    {
        var isPref := isPrefix(sub, str[i..]);
        if isPref
        {
            return true;
        }
        i := i-1;
    }
    return false;
}

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}


method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
    if( |str1| < k || |str2| < k){
        return false;
    }
    var i := |str1| - k;
    while i >= 0
      decreases i
      invariant i >= -1 
      invariant forall j :: i < j <= |str1| - k ==> !isSubstringPredicate(str1[j..][..k], str2)
    {
        var isSub := isSubstring(str1[i..][..k], str2);
        if isSub 
        {
            return true;
        }
        i := i-1;
    }
    return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
{
    
  var i := |str1|;

  while i > 0
  decreases i
  {
    var ans := haveCommonKSubstring(i, str1, str2);
    if ans {
       return i;
    }
    i := i -1;
  }

  return 0;

}

method Main()
{
  // some testing
  var pre := "pre";
  var str := "preadasda";
  var ans := isPrefix(pre, str);
  print ans;
  ans := isPrefix("abab", "abacadae");
  print ans;
  ans := isPrefix("abab", "ab");
  print ans;
}