module Collections {

    trait OMDataStructTrait
    {
        ghost var omDsSeq: seq<int>;

        method addBefore(x: int, y: int)
            // Check y exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] == y
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != x
            // Check x's position is less than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i] == x && omDsSeq[j] == y

        method addAfter(x: int, y: int)
            // Check y exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] == y
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != x
            // Check x's position is greater than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i] == y && omDsSeq[j] == x

        method add(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != x
            // Check x exists random position in DS
            ensures exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] == x

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exists i :: 0 <= i < |omDsSeq| && ((omDsSeq[i] == x && exist == true) || (omDsSeq[i] != x && exist == false))

        method before(x: int, y: int) returns (isBefore: bool)
            // Checks x and y are different values
            requires x != y
            // Check x exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] == x
            // Check y exists in DS
            requires exists j :: 0 <= j < |omDsSeq| && omDsSeq[j] == y
            // If x's position is less than y's position then return true otherwise false
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && ((omDsSeq[i] == x && omDsSeq[j] == y && isBefore == true) || (omDsSeq[i] == y && omDsSeq[j] == x && isBefore == false))

        method append(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != x
            // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
            ensures ((|omDsSeq| == 1 && omDsSeq[0] == x) || (|omDsSeq| > 1 && omDsSeq[|omDsSeq|-1] == x))

        method prepend(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != x
            // Check x is at the start of the DS always
            ensures omDsSeq[0] == x

        method remove(x: int)
            // Check x exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] == x
            // Check x doesn't exist in DS
            ensures forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != x
    }
    
}