include "../../../Abstract/utils/Collections.dfy" 

function method MapConcat_AllowSameKVPair<T(!new), U>(m1:map<T, U>, m2:map<T, U>) : (result:map<T, U>)
	requires forall k1, k2 :: k1 in m1 && k2 in m2 && k1 == k2
                ==> m1[k1] == m2[k2]
        // Requirement: If m1 and m2 have a same key, then the key maps to the same value in the two maps

    ensures forall k :: k in result <==> k in m1 || k in m2
	ensures forall k :: k in result
				==> (k in m1 ==> result[k] == m1[k]) &&
					(k in m2 ==> result[k] == m2[k])
{
	map i | i in (MapGetKeys(m1) + MapGetKeys(m2)) :: if i in m1 then m1[i] else m2[i]
}

predicate IsEmptySet<T>(s:set<T>)
{
    s == {}
}