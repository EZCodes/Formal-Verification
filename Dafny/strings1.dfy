method isPrefix(pre: string, str: string) returns (res: bool)
requires |str| >= |pre|
{
 var i := 0;  
 while i < |pre|
 decreases |pre| - i
 invariant i <= |pre|
 {
     if pre[i] != str[i]
     {
         return false;
     }
     i := i+1;
 }
 return true;
}

method isSubstring(sub: string, str: string) returns (res:bool)
requires |str| >= |sub|
{
    var i := |str| - |sub|;
    while i >= 0 
    decreases i
    invariant i >= -1
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

method haveCommonSubstring(k: nat, str1: string, str2: string) returns (found: bool)
requires k <= |str1| && k <= |str2|
{
    // I don't think it matters which string we go through
    var i := |str1| - k;
    while i >= 0
    decreases i
    invariant i >= -1 
    {
        var isSub := isSubstring(str1[i..i+k], str2);
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
 // same just while through lengths (first length is shorter of strings) 
}