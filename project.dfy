/**
    om - Order Maintained
    ds - Data Structure
 */
module Collections {
    
    class Node {
        var omLabel: int;
        var omValue: int;

        var previous: Node?;
        var next: Node?;

        var index: int;

        constructor (omLbl: int, omVal: int, idx: int)
            ensures omLabel == omLbl && omValue == omVal && index == idx
        {
            new;
            omLabel := omLbl;
            omValue := omVal;

            index := idx;
        }
    }

    trait OMDataStructTrait {
        var maxCapacity: int;
        var omDS: Node?;

        ghost var omDsSeq: seq<Node>;

        method addBefore(x: int, yNode: Node)
            // Check y exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == yNode.omValue
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue != x
            // Check x's position is less than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i].omValue == x && omDsSeq[j].omValue == yNode.omValue
            modifies yNode, yNode.previous, omDS, omDsSeq

        method addAfter(x: int, yNode: Node)
            // Check y exists in DS
            requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == yNode.omValue
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue != x
            // Check x's position is greater than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i].omValue == yNode.omValue && omDsSeq[j].omValue == x
            modifies omDS, omDsSeq, yNode, yNode.next

        method add(x: int)
            // Check x doesn't exist in DS
            requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue != x
            // Check x exists random position in DS
            ensures exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x
            modifies omDS

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == false || ((exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x) && exist == true)

        // method before(x: int, y: int) returns (isBefore: bool)
        //     // Checks x and y are different values
        //     requires x != y
        //     // Check x exists in DS
        //     requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue == x
        //     // Check y exists in DS
        //     requires exists j :: 0 <= j < |omDsSeq| && omDsSeq[j] != null && omDsSeq[j].omValue == y
        //     // If x's position is less than y's position then return true otherwise false
        //     ensures exists i,j :: 0 <= i < j < |omDsSeq| && ((((omDsSeq[i] != null && omDsSeq[i].omValue == x) && (omDsSeq[j] != null && omDsSeq[j].omValue == y)) && isBefore == true) || isBefore == false)

        // method append(x: int)
        //     // Check x doesn't exist in DS
        //     requires forall i :: 0 <= i < |omDsSeq| && (omDsSeq[i] != null && omDsSeq[i].omValue != x)
        //     // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
        //     ensures ((|omDsSeq| == 1 && (omDsSeq[0] != null && omDsSeq[0].omValue == x)) || (|omDsSeq| > 1 && (exists i :: 0 <= i < |omDsSeq|-1 && ((omDsSeq[i] != null && omDsSeq[i+1] == null) && omDsSeq[i].omValue == x))))
        //     modifies omDsSeq

        // method prepend(x: int)
        //     // At least 1 position should be empty
        //     requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] == null
        //     // Last element should be null
        //     requires |omDsSeq| > 0 && omDsSeq[|omDsSeq|-1] == null
        //     // Check x doesn't exist in DS
        //     requires forall i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue != x
        //     // Check x is at the start of the DS always
        //     ensures |omDsSeq| > 0 && omDsSeq[0] != null && omDsSeq[0].omValue == x
        //     modifies omDsSeq

        // method remove(x: int)
        //     // Check x exists in DS
        //     requires exists i :: 0 <= i < |omDsSeq| && omDsSeq[i] != null && omDsSeq[i].omValue == x
        //     // Check each value is unique
        //     requires forall i :: 0 <= i < |omDsSeq|-1 && omDsSeq[i] != null && (forall j :: i < j < |omDsSeq| && omDsSeq[j] != null && omDsSeq[i].omValue != omDsSeq[j].omValue)
        //     // Check x doesn't exist in DS
        //     ensures forall i :: 0 <= i < |omDsSeq| && ((omDsSeq[i] != null && omDsSeq[i].omValue != x) || omDsSeq[i] == null)
        //     modifies omDsSeq
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
            var node0 := new Node(0, 11, 0);
            var node1 := new Node(4, 46, 1);
            var node2 := new Node(8, 30, 2);
            var node3 := new Node(12, 4, 3);

            omDS := node0;
            node0.next := node1;
            node1.next := node2;
            node2.next := node3;
            node3.next := null;

            node3.previous := node2;
            node2.previous := node1;
            node1.previous := node0;
            node0.previous := null;

            omDsSeq := [node0, node1, node2, node3];
        }

        method addBefore(x: int, yNode: Node)
            // Check x's position is less than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i].omValue == x && omDsSeq[j].omValue == yNode.omValue
            ensures yNode.previous != null && x == yNode.previous.omValue
            modifies yNode, yNode.previous, omDS, omDsSeq
        {
            var xNode: Node;

            if(yNode.previous != null) {

                var previousNode: Node := yNode.previous;
                var xLabel := (yNode.previous.omLabel + yNode.omLabel) / 2;
                
                xNode := new Node(xLabel, x, yNode.index);

                xNode.previous := previousNode;
                xNode.next := yNode;
                yNode.previous := xNode;
                previousNode.next := xNode;
                
                // TODO: Later if time is enough
                // reIndex(omDS);

            } else {
                // Add before value to starting spot should relabel.
                var xLabel := (0 + yNode.omLabel) / 2;
                
                xNode := new Node(xLabel, x, 0);

                xNode.next := yNode;
                yNode.previous := xNode;

                // TODO: Later if time is enough
                // relabel();
            }

            omDsSeq := omDsSeq[..yNode.index] + [xNode] + omDsSeq[yNode.index..];
        }

        // method reIndex(omDS: Node?)
        //     modifies omDS
        // {
        //     var currentNode: Node? := omDS;
        //     var index: int := 0;

        //     while(currentNode != null)
        //         decreases |omDsSeq| - index
        //     {
        //         currentNode.index := index;
        //         index := index + 1;
        //         currentNode := currentNode.next;
        //     }
        // }

        // method relabel()
        //     modifies omDS
        // {
        //     index := 0;
        //     var newLabel: int, newPos := 0, 0;
        //     while(index < omDS.Length)
        //         invariant 0 <= index <= omDS.Length
        //         decreases omDS.Length - index
        //         modifies omDS
        //     {
        //         if(omDS[index] != null && newPos <= index) {
        //             omDS[newPos] := new Node(newLabel, omDS[index].omValue);

        //             newLabel := newLabel + currentNumElements;
        //             newPos := newPos + 1;
        //         }

        //         index := index + 1;
        //     }
        // }

        method addAfter(x: int, yNode: Node)
            // Check x's position is greater than y's position
            ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i].omValue == yNode.omValue && omDsSeq[j].omValue == x
            modifies omDS, omDsSeq, yNode, yNode.next
        {
            var xNode: Node;

            if(yNode.next != null) {

                var nextNode: Node := yNode.next;
                var xLabel := (yNode.omLabel + yNode.next.omLabel) / 2;
                
                xNode := new Node(xLabel, x, yNode.index+1);

                xNode.next := nextNode;
                xNode.previous := yNode;
                yNode.next := xNode;
                nextNode.previous := xNode;
                
                // TODO: Later if time is enough
                // reIndex(omDS);

            } else {
                // Add after value to end spot should not relabel.
                var listSize: int := yNode.index + 1;
                var xLabel := (yNode.omLabel + (listSize * listSize) - 1) / 2;
                
                xNode := new Node(xLabel, x, listSize);

                xNode.previous := yNode;
                yNode.next := xNode;
            }

            omDsSeq := omDsSeq[..yNode.index+1] + [xNode] + omDsSeq[yNode.index+1..];
        }

        method getSize(list: Node?) returns (size: int)
        {
            size := 0;
            var node: Node? := list;
            while(node != null)
            {
                size := size + 1;
                node := node.next;
            }
        }

        method getNodeAtIndex(list: Node?, index: int) returns (node: Node)
        {
            var iNode: Node? := list;
            while(iNode != null)
                invariant forall i :: 0 <= i < |omDsSeq| ==> iNode != null && iNode.index == i
            {
                if(iNode.index == index) {
                    node := iNode;
                    break;
                }

                iNode := iNode.next;
            }
        }

        method add(x: int)
            // Check x exists random position in DS
            ensures exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x
            modifies omDS
        {
            var randomIndex: int := 0;
            var listSize: int := getSize(omDS);
            randomIndex := if listSize != 0 then (randomNumberGlobal + randomIndex) % listSize else 0;

            var yIndex: int := randomIndex;
            var yNode: Node;
            var xLabel: int;
            var xNode: Node;
            if(listSize == 0) {
                xLabel := 1; // Relabelling should be triggered in the next element addition
                xNode := new Node(xLabel, x, 0);
                omDS := xNode;

            } else if(yIndex == listSize-1) {
                yNode := getNodeAtIndex(omDS, yIndex);
                xLabel := (yNode.omLabel + (listSize * listSize) - 1) / 2;
                xNode := addValAtIndex(yNode, xLabel, x);

            } else {
                yNode := getNodeAtIndex(omDS, yIndex);
                var yNodeNext: Node := getNodeAtIndex(omDS, yIndex + 1);
                xLabel := (yNode.omLabel + yNodeNext.omLabel) / 2;
                xNode := addValAtIndex(yNode, xLabel, x);
            }

            omDsSeq := omDsSeq[..yNode.index+1] + [xNode] + omDsSeq[yNode.index+1..];
        }

        method addValAtIndex(yNode: Node, xLabel: int, x: int) returns (xNode: Node)
            modifies yNode, yNode.next
        {
            xNode := new Node(xLabel, x, yNode.index + 1);
            if(yNode.next != null) {

                var nextNode: Node := yNode.next;
                yNode.next := xNode;
                xNode.previous := yNode;
                xNode.next := nextNode;
                nextNode.previous := xNode;
            } else {
                
                yNode.next := xNode;
                xNode.previous := yNode;
            }
        }

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == false || ((exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x) && exist == true)
        {
            var node: Node? := getNodeForValue(omDS, x);
            if(node != null) {
                exist := true;
            } else {
                exist := false;
            }
        }

        method getNodeForValue(list: Node?, x: int) returns (node: Node?)
            ensures node == null || (exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x && node == omDsSeq[i])
        {
            node := null;
            var iNode: Node? := list;
            while(iNode != null)
                invariant forall i :: 0 <= i < |omDsSeq| ==> iNode != null && iNode.index == i
            {
                if(iNode.omValue == x) {
                    node := iNode;
                    break;
                }

                iNode := iNode.next;
            }
        }

        // method before(x: int, y: int) returns (isBefore: bool)
        //     // Checks x and y are different values
        //     requires x != y
        //     // Check x exists in DS
        //     requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue == x
        //     // Check y exists in DS
        //     requires exists j :: 0 <= j < omDS.Length && omDS[j] != null && omDS[j].omValue == y
        //     // If x's position is less than y's position then return true otherwise false
        //     ensures exists i,j :: 0 <= i < j < omDS.Length && ((((omDS[i] != null && omDS[i].omValue == x) && (omDS[j] != null && omDS[j].omValue == y)) && isBefore == true) || isBefore == false)
        // {
        //     var xIndex: int := findIndex(x);
        //     var yIndex: int := findIndex(y);

        //     if(xIndex < yIndex) {
        //         isBefore := true;
        //     } else {
        //         isBefore := false;
        //     }
        // }

        // method append(x: int)
        //     // Check x doesn't exist in DS
        //     requires forall i :: 0 <= i < omDS.Length && (omDS[i] != null && omDS[i].omValue != x)
        //     // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
        //     ensures ((omDS.Length == 1 && (omDS[0] != null && omDS[0].omValue == x)) || (omDS.Length > 1 && (exists i :: 0 <= i < omDS.Length-1 && ((omDS[i] != null && omDS[i+1] == null) && omDS[i].omValue == x))))
        //     modifies omDS
        // {
        //     var index: int := 0;
        //     while(index < omDS.Length && omDS[index] != null)
        //         invariant 0 <= index <= omDS.Length
        //         decreases omDS.Length - index
        //     {
        //         index := index + 1;
        //     }

        //     var numElements: int := index - 1;
        //     var appendLabel: int := (numElements * numElements) - 1;
        //     omDS[index] := new Node(appendLabel, x);
        // }

        // method prepend(x: int)
        //     // At least 1 position should be empty
        //     requires exists i :: 0 <= i < omDS.Length && omDS[i] == null
        //     // Last element should be null
        //     requires omDS.Length > 0 && omDS[omDS.Length-1] == null
        //     // Check x doesn't exist in DS
        //     requires forall i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue != x
        //     // Check x is at the start of the DS always
        //     ensures omDS.Length > 0 && omDS[0] != null && omDS[0].omValue == x
        //     modifies omDS
        // {
        //     addValAtIndex(0, x, 0);

        //     relabel();
        // }

        // method remove(x: int)
        //     // Check x exists in DS
        //     requires exists i :: 0 <= i < omDS.Length && omDS[i] != null && omDS[i].omValue == x
        //     // Check each value is unique
        //     requires forall i :: 0 <= i < omDS.Length-1 && omDS[i] != null && (forall j :: i < j < omDS.Length && omDS[j] != null && omDS[i].omValue != omDS[j].omValue)
        //     // Check x doesn't exist in DS
        //     ensures forall i :: 0 <= i < omDS.Length && ((omDS[i] != null && omDS[i].omValue != x) || omDS[i] == null)
        //     modifies omDS
        // {
        //     var index: int := findIndex(x);

        //     omDS[index] := null;
        //     // Should be relabled since we have assumed all the elements are in the 
        //     // starting half of the array then null
        //     // (can be either empty or full array too)
        //     relabel();
        // }
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