module Collections {
    
    class Node {
        var omLabel: int;
        var omValue: int;

        constructor (omLbl: int, omVal: int)
        {
            new;
            omLabel := omLbl;
            omValue := omVal;
        }
    }

    trait OMDataStructTrait
    {
        var maxCapacity: int;
        var omDS: array<Node?>;

        ghost var omDsSeq: seq<Node?>;

        method addBefore(x: int, y: int)
            // Check y exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue == y
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue != x
            // Check x's position is less than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && (omDsSeq[i] != null && omDsSeq[i].omValue == x) && (omDsSeq[j] != null && omDsSeq[j].omValue == y)
            modifies omDsSeq

        method addAfter(x: int, y: int)
            // Check y exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue == y
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue != x
            // Check x's position is greater than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && (omDsSeq[i] != null && omDsSeq[i].omValue == y) && (omDsSeq[j] != null && omDsSeq[j].omValue == x)
            modifies omDsSeq

        method add(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue != x
            // Check x exists random position in DS
            ensures exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue == x
            modifies omDsSeq

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == false || ((exists i :: 0 <= i < |omDsSeq| && (omDsSeq[i] != null && omDsSeq[i].omValue == x)) && exist == true)

        method before(x: int, y: int) returns (isBefore: bool)
            // Checks x and y are different values
            requires x != y
            // Check x exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue == x
            // Check y exists in DS
            requires exists j :: 0 <= j < |omDsSeq| && omDsSeq[j] != null && omDsSeq[j].omValue == y
            // If x's position is less than y's position then return true otherwise false
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && ((((omDsSeq[i] != null && omDsSeq[i].omValue == x) && (omDsSeq[j] != null && omDsSeq[j].omValue == y)) && isBefore == true) || isBefore == false)

        method append(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && (omDsSeq[i] != null && omDsSeq[i].omValue != x)
            // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
            ensures ((|omDsSeq| == 1 && (omDsSeq[0] != null && omDsSeq[0].omValue == x)) || (|omDsSeq| > 1 && (exists i :: 0 <= i < |omDsSeq|-1 && ((omDsSeq[i] != null && omDsSeq[i+1] == null) && omDsSeq[i].omValue == x))))
            modifies omDsSeq

        method prepend(x: int)
            // At least 1 position should be empty
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] == null
            // Last element should be null
            requires |omDsSeq| > 0 && omDsSeq[|omDsSeq|-1] == null
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue != x
            // Check x is at the start of the DS always
            ensures |omDsSeq| > 0 && omDsSeq[0] != null && omDsSeq[0].omValue == x
            modifies omDsSeq

        method remove(x: int)
            // Check x exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue == x
            // Check each value is unique
            requires forall i :: 0 <= i < |omDsSeq|-1 && omDsSeq[i] != null && (forall j :: i < j < |omDsSeq| && omDsSeq[j] != null && omDsSeq[i].omValue != omDsSeq[j].omValue)
            // Check x doesn't exist in DS
            ensures forall i :: 0 <= i < |omDsSeq| && ((omDsSeq[i] != null && omDsSeq[i].omValue != x) || omDsSeq[i] == null)
            modifies omDsSeq
    }

    class OMDataStruct extends OMDataStructTrait {
        var randomNumberGlobal: int;

        constructor (maxCap: int)
            requires maxCap >= 0
        {
            new;
            maxCapacity := maxCap;
            randomNumberGlobal := 1;
            // Temporary to test. Remove below.
            maxCapacity := 16;
            // TODO: Restrict max capacity to N
            // TODO: label capacity - N^2
            // Minor scenarios are not covered since they can't be added within time limit. E.g.
            //      1. Major index removed then addBefore/addAfter/add will not insert to major indices.
            // Insert before 0 triggers relabeling. Thus, not covered in initial version.
            // [0, 4, 8, 12] - labels
            // [11, 46, 30, 4] - values
            var node0 := new Node(0, 11);
            var node1 := new Node(4, 46);
            var node2 := new Node(8, 30);
            var node3 := new Node(12, 4);

            omDS := new Node?[maxCapacity];
            omDS[0] := node0;
            omDS[1] := node1;
            omDS[2] := node2;
            omDS[3] := node3;

            omDsSeq := computerOmDsSeq(omDS, omDS.Length-1);
        }

        function computerOmDsSeq(omDS: array<Node?>, index: nat): seq<Node?>
            requires 0 <= index < omDS.Length
            reads omDS
        {
            if index == 0 then [omDS[0]] else computerOmDsSeq(omDS, index-1) + [omDS[index]]
        }

        // Will be used till a memory pointer manupulation way is found.
        method findIndex(x: int) returns (index: int)
            // Check y exists in the array
            requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && x == omDS[i].omValue
            ensures 0 <= index < omDS.Length
        {
            index := 0;
            while(index < omDS.Length)
                // Swapping 2 invariants give an error
                invariant 0 <= index <= omDS.Length
                invariant forall i :: 0 <= i < index ==> omDS[i] == null || (omDS[i] != null && omDS[i].omValue != x)
                decreases omDS.Length - index
            {
                if(omDS[index] != null && omDS[index].omValue == x) {
                    break;
                }

                index := index + 1;
            }
        }

        // This method of copying values and labels was added due to seq are immutable and arrays are fixed length.
        // Method params are immutable.
        method addValBeforeIndex(yIndex: int, x: int, xLabel: int)
            requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && i == yIndex
            modifies omDS
        {
            var index: int := yIndex;

            var yNode: Node := omDS[index];
            omDS[index] := new Node(xLabel, x);
            index := index + 1;

            // Can't assert below. Should be a limitation of Dafny
            // assert omDS[yIndex].omValue == x;

            while(index < omDS.Length)
                invariant yIndex+1 <= index <= omDS.Length
                invariant forall i :: yIndex+1 <= i < index ==> omDS[i] != null
                decreases omDS.Length - index
            {
                var yNodeNext := omDS[index];
                omDS[index] := yNode;
                if(yNodeNext == null) {
                    break;
                } else {
                    yNode := yNodeNext;
                }

                index := index + 1;
            }

            // Can't assert below. Should be a limitation of Dafny
            // assert exists i :: 0 <= i < omDS.Length ==> omDS[i] != null && omDS[i].omValue == x;
        }

        method addBefore(x: int, y: int)
            // Check y exists in DS
            requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue == y
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue != x
            // Check x's position is less than y's position
            modifies omDS
        {

            var yIndex: int := findIndex(y);
            // yIndex = 0 should trigger relabelling. Thus, not covered in initial version.
            if(yIndex > 0) {
                var xLabel := (omDS[yIndex - 1].omLabel + omDS[yIndex].omLabel) / 2;
                addValBeforeIndex(yIndex, x, xLabel);
            }

            // Can't assert below. Should be a limitation of Dafny
            // assert exists i :: 0 <= i < omDS.Length ==> omDS[i] != null && y == omDS[i].omValue;
            // assert exists i :: 0 <= i < omDS.Length && omDS[i] != null && x == omDS[i].omValue;
        }

        method addValAfterIndex(yIndex: int, x: int, xLabel: int)
            requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && i == yIndex
            modifies omDS
        {
            var index: int := yIndex + 1;

            // Otherwise needs relabelling or max capacity is reached.
            if(index < omDS.Length) {

                var yNodeNext: Node? := omDS[index];
                omDS[index] := new Node(xLabel, x);
                index := index + 1;

                // Can't assert below. Should be a limitation of Dafny
                // assert omDS[yIndex+1].omValue == x;

                while(yNodeNext != null && index < omDS.Length)
                    invariant yIndex+2 <= index <= omDS.Length
                    invariant forall i :: yIndex+2 <= i < index ==> omDS[i] != null
                    decreases omDS.Length - index
                {
                    var yNodeNextNext := omDS[index];
                    omDS[index] := yNodeNext;
                    if(yNodeNextNext == null) {
                        break;
                    } else {
                        yNodeNext := yNodeNextNext;
                    }

                    index := index + 1;
                }

                // Can't assert below. Should be a limitation of Dafny
                // assert exists i :: 0 <= i < omDS.Length ==> omDS[i] != null && omDS[i].omValue == x;
            }
        }

        method addAfter(x: int, y: int)
            // Check y exists in the array
            requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && y == omDS[i].omValue
            // Check x doesn't exist in the array
            requires forall i :: 0 <= i < omDS.Length && omDS[i] != null && x != omDS[i].omValue
            modifies omDS
        {
            var yIndex: int := findIndex(y);
            // yIndex = 0 should trigger relabelling. Thus, not covered in initial version.
            var xLabel: int := 0;
            if(yIndex == omDS.Length-1) {
                xLabel := (omDS[yIndex].omLabel + (omDS.Length * omDS.Length)) / 2;
            } else {
                xLabel := (omDS[yIndex].omLabel + omDS[yIndex + 1].omLabel) / 2;
            }
            addValAfterIndex(yIndex, x, xLabel);
        }

        method addValAtIndex(yIndex: int, x: int, xLabel: int)
            requires 0 <= yIndex < omDS.Length
            modifies omDS
        {
            var index: int := yIndex;

            var yNode: Node? := omDS[index];
            omDS[index] := new Node(xLabel, x);
            index := index + 1;

            // Can't assert below. Should be a limitation of Dafny
            // assert omDS[yIndex].omValue == x;

            while(yNode != null && index < omDS.Length)
                invariant yIndex+1 <= index <= omDS.Length
                invariant forall i :: yIndex+1 <= i < index ==> omDS[i] != null
                decreases omDS.Length - index
            {
                var yNodeNext := omDS[index];
                omDS[index] := yNode;
                if(yNodeNext == null) {
                    break;
                } else {
                    yNode := yNodeNext;
                }

                index := index + 1;
            }

            // Can't assert below. Should be a limitation of Dafny
            // assert exists i :: 0 <= i < omDS.Length ==> omDS[i] != null && omDS[i].omValue == x;
        }

        method add(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue != x
            modifies omDS
        {
            var randomNumber: int := 0;
            randomNumber := if omDS.Length != 0 then (randomNumberGlobal + randomNumber) % omDS.Length else 0;
            assert 0 <= randomNumber < omDS.Length;
            var yIndex: int := randomNumber;
            var xLabel: int;
            if(omDS.Length == 0) {
                xLabel := 1; // Relabelling should be triggered in the next element addition
            } else if(yIndex == omDS.Length-1) {
                xLabel := (omDS[yIndex].omLabel + (omDS.Length * omDS.Length)) / 2;
            } else {
                xLabel := (omDS[yIndex].omLabel + omDS[yIndex + 1].omLabel) / 2;
            }
            randomNumber := randomNumber + 1;
            
            addValAtIndex(yIndex, x, xLabel);
        }

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == false || ((exists i :: 0 <= i < omDS.Length && (omDS[i] != null && omDS[i].omValue == x)) && exist == true)
        {
            exist := false;
            var index: int := 0;
            while(index < omDS.Length && omDS[index] != null)
                invariant 0 <= index <= omDS.Length
                invariant forall i :: 0 <= i < index ==> omDS[i] != null && omDS[i].omValue != x
                decreases omDS.Length - index
            {
                if(omDS[index].omValue == x) {
                    exist := true;
                    break;
                }

                index := index + 1;
            }

            assert if exist == true then omDS[index].omValue == x else index == omDS.Length || omDS[index] == null;
        }

        method before(x: int, y: int) returns (isBefore: bool)
            // Checks x and y are different values
            requires x != y
            // Check x exists in DS
            requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue == x
            // Check y exists in DS
            requires exists j :: 0 <= j < omDS.Length && omDS[j] != null && omDS[j].omValue == y
            // If x's position is less than y's position then return true otherwise false
            ensures exists i,j :: 0 <= i < j < omDS.Length && ((((omDS[i] != null && omDS[i].omValue == x) && (omDS[j] != null && omDS[j].omValue == y)) && isBefore == true) || isBefore == false)
        {
            isBefore := false;
            var index: int := 0;
            var xIndex, yIndex := -1, -1;

            while(index < omDS.Length && omDS[index] != null)
                invariant 0 <= index <= omDS.Length
                invariant forall i :: 0 <= i < index ==> omDS[i] != null && omDS[i].omValue != x
                decreases omDS.Length - index
            {
                if(omDS[index].omValue == x) {
                    xIndex := index;
                    break;
                }

                index := index + 1;
            }

            ghost var xIndexPos: int := index;

            while(index < omDS.Length && omDS[index] != null)
                invariant xIndexPos <= index <= omDS.Length
                invariant forall i :: xIndexPos <= i < index ==> omDS[i] != null && omDS[i].omValue != y
                decreases omDS.Length - index
            {
                if(omDS[index].omValue == y) {
                    yIndex := index;
                    break;
                }

                index := index + 1;
            }

            if(xIndex < yIndex) {
                isBefore := true;
            }

            assert if isBefore == true then xIndex < yIndex else xIndex >= yIndex;
        }

        method append(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < omDS.Length && (omDS[i] != null && omDS[i].omValue != x)
            // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
            ensures ((omDS.Length == 1 && (omDS[0] != null && omDS[0].omValue == x)) || (omDS.Length > 1 && (exists i :: 0 <= i < omDS.Length-1 && ((omDS[i] != null && omDS[i+1] == null) && omDS[i].omValue == x))))
            modifies omDS
        {
            var index: int := 0;
            while(index < omDS.Length && omDS[index] != null)
                invariant 0 <= index <= omDS.Length
                decreases omDS.Length - index
            {
                index := index + 1;
            }

            var numElements: int := index - 1;
            var appendLabel: int := (numElements * numElements) - 1;
            omDS[index] := new Node(appendLabel, x);
        }

        method prepend(x: int)
            // At least 1 position should be empty
            requires exists i :: 0 <= i < omDS.Length && omDS[i] == null
            // Last element should be null
            requires omDS.Length > 0 && omDS[omDS.Length-1] == null
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue != x
            // Check x is at the start of the DS always
            ensures omDS.Length > 0 && omDS[0] != null && omDS[0].omValue == x
            modifies omDS
        {
            // Move all elements to the right by 1 position, add new element to the start
            // then relabel
            var index: int := 0;
            var tempNode: Node? := omDS[0];
            omDS[0] := new Node(0, x);
            while(index < omDS.Length-1)
                invariant 0 <= index <= omDS.Length-1
                decreases omDS.Length-1 - index
            {
                var tempNodeInner: Node? := omDS[index+1];
                omDS[index+1] := tempNode;
                tempNode := tempNodeInner;

                index := index + 1;
            }

            relabel();
        }

        method relabel()
            modifies omDS
        {
            var currentNumElements: int := 0;
            var index: int := 0;
            while(index < omDS.Length)
                invariant 0 <= index <= omDS.Length
                decreases omDS.Length - index
            {
                if(omDS[index] != null) {
                    currentNumElements := currentNumElements + 1;
                }

                index := index + 1;
            }

            index := 0;
            var newLabel: int, newPos := 0, 0;
            while(index < omDS.Length)
                invariant 0 <= index <= omDS.Length
                decreases omDS.Length - index
                modifies omDS
            {
                if(omDS[index] != null && newPos <= index) {
                    omDS[newPos] := new Node(newLabel, omDS[index].omValue);

                    newLabel := newLabel + currentNumElements;
                    newPos := newPos + 1;
                }

                index := index + 1;
            }
        }

        method remove(x: int)
            // Check x exists in DS
            requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue == x
            // Check each value is unique
            requires forall i :: 0 <= i < omDS.Length-1 && omDS[i] != null && (forall j :: i < j < omDS.Length && omDS[j] != null && omDS[i].omValue != omDS[j].omValue)
            // Check x doesn't exist in DS
            ensures forall i :: 0 <= i < omDS.Length && ((omDS[i] != null && omDS[i].omValue != x) || omDS[i] == null)
            modifies omDS
        {
            var index: int, xIndex: int := 0, -1;
            while(index < omDS.Length)
                invariant 0 <= index <= omDS.Length
                invariant forall i :: 0 <= i < index ==> (omDS[i] != null && omDS[i].omValue != x) || omDS[i] == null
                decreases omDS.Length - index
            {
                // if condition can be moved to while condition where all verification fails.
                if(omDS[index] != null && omDS[index].omValue == x) {
                    break;
                }

                index := index + 1;
            }
            assert omDS[index].omValue == x;

            omDS[index] := null;
            // Should be relabled since we have assumed all the elements are in the 
            // starting half of the array then null
            // (can be either empty or full array too)
            relabel();
        }
    }
    
}

module Runner {
    // import c = Collections

    // method main()
    // {
    //     var omDataStruct := new c.OMDataStruct(16);

    //     omDataStruct.addBefore(8, 30);
    // }
}