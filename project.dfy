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

        ghost var index: int;

        constructor (omLbl: int, omVal: int, ghost idx: int)
            ensures omLabel == omLbl && omValue == omVal && index == idx
        {
            new;
            omLabel := omLbl;
            omValue := omVal;

            index := idx;
        }
    }

    trait OMDataStructTrait {
        var omDS: Node?;

        ghost var omDsSeq: seq<int>;
        ghost var oldOmDsSeq: seq<int>;

        method addBefore(x: int, yNode: Node)
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            requires oldOmDsSeq == omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x's position is less than y's position
            ensures exists fstSeq, scndSeq :: oldOmDsSeq == fstSeq + [yNode.omValue] + scndSeq && omDsSeq == fstSeq + [x, yNode.omValue] + scndSeq
            modifies yNode, yNode.previous, omDS

        method addAfter(x: int, yNode: Node)
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            requires oldOmDsSeq == omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x's position is greater than y's position
            ensures exists fstSeq, scndSeq :: oldOmDsSeq == fstSeq + [yNode.omValue] + scndSeq && omDsSeq == fstSeq + [x, yNode.omValue] + scndSeq

        method add(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x exists random position in DS
            ensures x in omDsSeq

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == (x in omDsSeq)

        method before(xNode: Node, yNode: Node) returns (isBefore: bool)
            // Checks x and y are different values
            requires xNode.omValue != yNode.omValue
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // If x's position is less than y's position then return true otherwise false
            ensures exists fstSeq, midSeq, scndSeq :: omDsSeq == fstSeq + [xNode.omValue] + midSeq + [yNode.omValue] + scndSeq

        method append(valSet: set<int>)
            // Check x doesn't exist in DS
            requires exists val :: val in valSet && val !in omDsSeq
            requires oldOmDsSeq == omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + scndSeq && oldOmDsSeq == fstSeq && val in scndSeq && val in valSet

        method prepend(valSet: set<int>)
            // Check x doesn't exist in DS
            requires exists val :: val in valSet && val !in omDsSeq
            requires oldOmDsSeq == omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x is at the start of the DS always
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + scndSeq && oldOmDsSeq == scndSeq && val in fstSeq && val in valSet

        method remove(xNode: Node)
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x doesn't exist in DS
            ensures xNode.omValue !in omDsSeq
    }

    // class OMDataStruct extends OMDataStructTrait {
    //     var randomNumberGlobal: int;

    //     constructor (maxCap: int)
    //         requires maxCap >= 0
    //     {
    //         new;
    //         maxCapacity := maxCap;
    //         randomNumberGlobal := 1;
    //         // Temporary to test. Remove below.
    //         maxCapacity := 16;
    //         // TODO: Restrict max capacity to N
    //         // TODO: label capacity - N^2
    //         // Minor scenarios are not covered since they can't be added within time limit. E.g.
    //         //      1. Major index removed then addBefore/addAfter/add will not insert to major indices.
    //         // Insert before 0 triggers relabeling. Thus, not covered in initial version.
    //         // [0, 4, 8, 12] - labels
    //         // [11, 46, 30, 4] - values
    //         var node0 := new Node(0, 11, 0);
    //         var node1 := new Node(4, 46, 1);
    //         var node2 := new Node(8, 30, 2);
    //         var node3 := new Node(12, 4, 3);

    //         omDS := node0;
    //         // tail := node3;
    //         node0.next := node1;
    //         node1.next := node2;
    //         node2.next := node3;
    //         node3.next := null;

    //         node3.previous := node2;
    //         node2.previous := node1;
    //         node1.previous := node0;
    //         node0.previous := null;

    //         omDsSeq := [node0, node1, node2, node3];
    //         // omDsSeq := computeOmDsSeq(omDS);
    //     }

    //     method addBefore(x: int, yNode: Node)
    //         // Check x's position is less than y's position
    //         ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i] == x && omDsSeq[j] == yNode.omValue
    //         ensures yNode.previous != null && x == yNode.previous.omValue
    //         modifies yNode, yNode.previous, omDS
    //     {
    //         var xNode: Node;

    //         if(yNode.previous != null) {

    //             var previousNode: Node := yNode.previous;
    //             var xLabel := (yNode.previous.omLabel + yNode.omLabel) / 2;
                
    //             xNode := new Node(xLabel, x, yNode.index);

    //             xNode.previous := previousNode;
    //             xNode.next := yNode;
    //             yNode.previous := xNode;
    //             previousNode.next := xNode;
                
    //             // TODO: Later if time is enough
    //             // reIndex(omDS);

    //         } else {
    //             // Add before value to starting spot should relabel.
    //             var xLabel := (0 + yNode.omLabel) / 2;
                
    //             xNode := new Node(xLabel, x, 0);

    //             xNode.next := yNode;
    //             yNode.previous := xNode;

    //             // TODO: Later if time is enough
    //             // relabel();
    //         }

    //         omDsSeq := omDsSeq[..yNode.index] + [xNode] + omDsSeq[yNode.index..];
    //     }

    //     // function computeOmDsSeq(node: Node?): seq<Node?>
    //     //     decreases node
    //     //     reads node
    //     // {
    //     //     if node.next == null then [node] else [node] + computeOmDsSeq(node.next)
    //     // }

    //     // method reIndex(omDS: Node?)
    //     //     modifies omDS
    //     // {
    //     //     var currentNode: Node? := omDS;
    //     //     var index: int := 0;

    //     //     while(currentNode != null)
    //     //         decreases |omDsSeq| - index
    //     //     {
    //     //         currentNode.index := index;
    //     //         index := index + 1;
    //     //         currentNode := currentNode.next;
    //     //     }
    //     // }

    //     // method relabel()
    //     //     modifies omDS
    //     // {
    //     //     index := 0;
    //     //     var newLabel: int, newPos := 0, 0;
    //     //     while(index < omDS.Length)
    //     //         invariant 0 <= index <= omDS.Length
    //     //         decreases omDS.Length - index
    //     //         modifies omDS
    //     //     {
    //     //         if(omDS[index] != null && newPos <= index) {
    //     //             omDS[newPos] := new Node(newLabel, omDS[index].omValue);

    //     //             newLabel := newLabel + currentNumElements;
    //     //             newPos := newPos + 1;
    //     //         }

    //     //         index := index + 1;
    //     //     }
    //     // }

    //     method addAfter(x: int, yNode: Node)
    //         // Check x's position is greater than y's position
    //         ensures exists i,j :: 0 <= i < j < |omDsSeq| && omDsSeq[i].omValue == yNode.omValue && omDsSeq[j].omValue == x
    //         modifies omDS, omDsSeq, yNode, yNode.next
    //     {
    //         var xNode: Node;

    //         if(yNode.next != null) {

    //             var nextNode: Node := yNode.next;
    //             var xLabel := (yNode.omLabel + yNode.next.omLabel) / 2;
                
    //             xNode := new Node(xLabel, x, yNode.index+1);

    //             xNode.next := nextNode;
    //             xNode.previous := yNode;
    //             yNode.next := xNode;
    //             nextNode.previous := xNode;
                
    //             // TODO: Later if time is enough
    //             // reIndex(omDS);

    //         } else {
    //             // Add after value to end spot should not relabel.
    //             var listSize: int := yNode.index + 1;
    //             var xLabel := (yNode.omLabel + (listSize * listSize) - 1) / 2;
                
    //             xNode := new Node(xLabel, x, listSize);

    //             xNode.previous := yNode;
    //             yNode.next := xNode;
    //         }

    //         omDsSeq := omDsSeq[..yNode.index+1] + [xNode] + omDsSeq[yNode.index+1..];
    //     }

    //     method getSize(list: Node?) returns (size: int)
    //     {
    //         size := 0;
    //         var node: Node? := list;
    //         while(node != null)
    //         {
    //             size := size + 1;
    //             node := node.next;
    //         }
    //     }

    //     function getSizeFunc(node: Node?): int
    //         reads node
    //         // PROBLEM: there's no way to get the size of the linked list
    //         // decreases omDsSeq[|omDsSeq|-1].index - node.index
    //     {
    //         if node == null then 0 else 1 + getSizeFunc(node.next)
    //     }

    //     method getNodeAtIndex(list: Node?, index: int) returns (node: Node)
    //     {
    //         var iNode: Node? := list;
    //         while(iNode != null)
    //             invariant iNode != null || iNode == null
    //         {
    //             if(iNode.index == index) {
    //                 node := iNode;
    //                 break;
    //             }

    //             iNode := iNode.next;
    //         }
    //     }

    //     method add(x: int)
    //         // Check x exists random position in DS
    //         ensures exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x
    //         modifies omDS
    //     {
    //         var randomIndex: int := 0;
    //         var listSize: int := getSize(omDS);
    //         randomIndex := if listSize != 0 then (randomNumberGlobal + randomIndex) % listSize else 0;

    //         var yIndex: int := randomIndex;
    //         var yNode: Node;
    //         var xLabel: int;
    //         var xNode: Node;
    //         if(listSize == 0) {
    //             xLabel := 1; // Relabelling should be triggered in the next element addition
    //             xNode := new Node(xLabel, x, 0);
    //             omDS := xNode;

    //         } else if(yIndex == listSize-1) {
    //             yNode := getNodeAtIndex(omDS, yIndex);
    //             xLabel := (yNode.omLabel + (listSize * listSize) - 1) / 2;
    //             xNode := addValAtIndex(yNode, xLabel, x);

    //         } else {
    //             yNode := getNodeAtIndex(omDS, yIndex);
    //             var yNodeNext: Node := getNodeAtIndex(omDS, yIndex + 1);
    //             xLabel := (yNode.omLabel + yNodeNext.omLabel) / 2;
    //             xNode := addValAtIndex(yNode, xLabel, x);
    //         }

    //         omDsSeq := omDsSeq[..yNode.index+1] + [xNode] + omDsSeq[yNode.index+1..];
    //     }

    //     method addValAtIndex(yNode: Node, xLabel: int, x: int) returns (xNode: Node)
    //         modifies yNode, yNode.previous
    //     {
    //         xNode := new Node(xLabel, x, yNode.index);
    //         if(yNode.previous != null) {

    //             var prevNode: Node := yNode.previous;
    //             yNode.previous := xNode;
    //             xNode.next := yNode;
    //             xNode.previous := prevNode;
    //             prevNode.next := xNode;
    //         } else {
                
    //             yNode.previous := xNode;
    //             xNode.next := yNode;
    //         }

    //         // TODO: should trigger relabel
    //         // reIndex();
    //     }

    //     method element(x: int) returns (exist: bool)
    //         // At some position, if x exists then return true otherwise false
    //         ensures exist == false || ((exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x) && exist == true)
    //     {
    //         var node: Node? := getNodeForValue(omDS, x);
    //         if(node != null) {
    //             exist := true;
    //         } else {
    //             exist := false;
    //         }
    //     }

    //     method getNodeForValue(list: Node?, x: int) returns (node: Node?)
    //         ensures node == null || (exists i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue == x && node == omDsSeq[i])
    //     {
    //         node := null;
    //         var iNode: Node? := list;
    //         while(iNode != null)
    //             invariant forall i :: 0 <= i < |omDsSeq| ==> iNode != null && iNode.index == i
    //         {
    //             if(iNode.omValue == x) {
    //                 node := iNode;
    //                 break;
    //             }

    //             iNode := iNode.next;
    //         }
    //     }

    //     method before(x: int, y: int) returns (isBefore: bool)
    //         // If x's position is less than y's position then return true otherwise false
    //         ensures exists i,j :: 0 <= i < j < |omDsSeq| && (((omDsSeq[i].omValue == x && omDsSeq[j].omValue == y) && isBefore == true) || isBefore == false)
    //     {
    //         var xNode: Node? := getNodeForValue(omDS, x);
    //         var yNode: Node? := getNodeForValue(omDS, y);

    //         if(xNode == null || yNode == null) {
    //             isBefore := false;
    //         } else if(xNode.index < yNode.index) {
    //             isBefore := true;
    //         } else {
    //             isBefore := false;
    //         }
    //     }

    //     method append(x: int)
    //         // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
    //         ensures (|omDsSeq| == 1 && omDsSeq[0].omValue == x) || (|omDsSeq| > 1 && omDsSeq[|omDsSeq|-1].omValue == x)
    //         modifies omDS
    //     {
    //         var node: Node? := omDS;
    //         if(node == null) {

    //             var numElements: int := 1;
    //             var appendLabel: int := ((numElements * numElements) - 1) / 2;
    //             var appendNode: Node := new Node(appendLabel, x, numElements);
    //             node.next := appendNode;

    //             omDsSeq := [appendNode];
    //         } else {

    //             while(node != null)
    //                 invariant node == null || node != null
    //                 decreases (if node == null then 0 else (getSizeFunc(omDS) - node.index))
    //                 modifies node, node.next
    //             {
    //                 if(node.next == null) {

    //                     var numElements: int := node.index + 1;
    //                     var appendLabel: int := (node.omLabel + (numElements * numElements) - 1) / 2;
    //                     var appendNode: Node := new Node(appendLabel, x, numElements);
    //                     node.next := appendNode;

    //                     omDsSeq := omDsSeq + [appendNode];

    //                     break;
    //                 }
    //                 node := node.next;
    //             }

    //             // TODO: relabel is needed, do it later
    //             // relabel();
    //         }
    //     }

    //     method prepend(x: int)
    //         // Check x is at the start of the DS always
    //         ensures |omDsSeq| > 0 && omDsSeq[0].omValue == x
    //         // ensures getSizeFunc(omDS) > 0 && omDS[0].omValue == x
    //         modifies omDS, omDsSeq, omDS.previous
    //     {
    //         if(omDS != null) {
    //             var xNode: Node := addValAtIndex(omDS, 0, x);

    //             omDsSeq := [xNode] + omDsSeq;
    //         } else {
    //             var xNode: Node := new Node(0, x, 0);
    //             omDS := xNode;

    //             omDsSeq := [xNode];
    //         }

    //         // TODO: relabel is needed, do it later
    //         // relabel();
    //     }

    //     method remove(x: int)
    //         // Check x doesn't exist in DS
    //         ensures forall i :: 0 <= i < |omDsSeq| && omDsSeq[i].omValue != x
    //         modifies omDS, omDsSeq
    //     {
    //         var iNode: Node? := omDS;
    //         while(iNode != null)
    //             invariant iNode != null || iNode == null
    //             modifies iNode.next, iNode.previous
    //         {
    //             if(iNode.omValue == x) {
                    
    //                 var nextNode: Node? := iNode.next;
    //                 var prevNode: Node? := iNode.previous;

    //                 if(prevNode != null) {
    //                     prevNode.next := nextNode;

    //                     if(nextNode != null) {
    //                         nextNode.previous := prevNode;
    //                     }
    //                 }
    //                 omDsSeq := omDsSeq[..iNode.index] + omDsSeq[iNode.index+1..];

    //                 break;
    //             }

    //             iNode := iNode.next;
    //         }

    //         // TODO: should trigger relabel
    //         // relabel();
    //     }
    // }
    
}

module Runner {
    import c = Collections

    method main()
    {
        // var omDataStruct := new c.OMDataStruct(16);

        // // [0, 4, 8, 12] - labels
        // // [11, 46, 30, 4] - values
        // var node0 := new c.Node(0, 11, 0);
        // var node1 := new c.Node(4, 46, 1);
        // var node2 := new c.Node(8, 30, 2);
        // var node3 := new c.Node(12, 4, 3);

        // omDataStruct.omDS := node0;
        // node0.next := node1;
        // node1.next := node2;
        // node2.next := node3;
        // node3.next := null;

        // node3.previous := node2;
        // node2.previous := node1;
        // node1.previous := node0;
        // node0.previous := null;

        // omDataStruct.omDsSeq := [node0, node1, node2, node3];

        // omDataStruct.addBefore(8, node2);
    }
}