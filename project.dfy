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

        // Can't make this a ghost var since while loop decrease clause.
        // But used for verification only.
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
        var head: Node;
        var tail: Node;

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
            modifies yNode, yNode.previous

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
            modifies yNode, yNode.next

        // Inserts x at the start of the linked list
        method add(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x exists random position in DS
            ensures x in omDsSeq
            modifies head, head.next

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
            // Check each value is unique
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq

        method prepend(valSet: set<int>)
            // Check x doesn't exist in DS
            requires exists val :: val in valSet && val !in omDsSeq
            requires oldOmDsSeq == omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x is at the start of the DS always
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + scndSeq && oldOmDsSeq == scndSeq && val in fstSeq && val in valSet
            // Check each value is unique
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq

        method remove(xNode: Node)
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x doesn't exist in DS
            ensures xNode.omValue !in omDsSeq
    }

    class OMDataStruct extends OMDataStructTrait {

        constructor ()
        {
            var headNode := new Node(0, 0, 0);
            var tailNode := new Node(0, 0, 0);
            head := headNode;
            tail := tailNode;
            new;
            // [0, 4, 8, 12] - labels
            // [11, 46, 30, 4] - values
            
            var node0 := new Node(4, 11, 0);
            var node1 := new Node(8, 46, 1);
            var node2 := new Node(12, 30, 2);
            var node3 := new Node(16, 4, 3);

            headNode.next := node0;
            node0.next := node1;
            node1.next := node2;
            node2.next := node3;
            node3.next := tailNode;

            tailNode.previous := node3;
            node3.previous := node2;
            node2.previous := node1;
            node1.previous := node0;
            node0.previous := headNode;

            var dsSize: int := tailNode.previous.index + 1;
            tailNode.omLabel := dsSize * (dsSize + 1);

            omDsSeq := [node0.omValue, node1.omValue, node2.omValue, node3.omValue];
            oldOmDsSeq := omDsSeq;
            assert tail.previous.index+1 == |omDsSeq|;
        }

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
            modifies yNode, yNode.previous
        {
            // yNode.previous always not null since it can be head node in the worst case.
            if(yNode.previous != null) {
                assert oldOmDsSeq == omDsSeq;

                var labelGap: int := yNode.omLabel - yNode.previous.omLabel;
                var xLabel: int := yNode.previous.omLabel + (labelGap / 2);
                var xNode: Node := new Node(xLabel, x, yNode.index);

                var prevNode: Node := yNode.previous;
                xNode.previous := prevNode;
                xNode.next := yNode;
                prevNode.next := xNode;
                yNode.previous := xNode;
            }

            omDsSeq := omDsSeq[..yNode.index] + [x] + omDsSeq[yNode.index..];
            assert tail.previous.index+1 == |omDsSeq|;
            assert omDsSeq[yNode.index-1] == x;

            // TODO:
            // reIndex();
        }

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
            modifies yNode, yNode.next
        {
            // yNode.next always not null since it can be tail node in the worst case.
            if(yNode.next != null) {
                assert oldOmDsSeq == omDsSeq;

                var labelGap: int := yNode.omLabel - yNode.next.omLabel;
                var xLabel: int := yNode.next.omLabel + (labelGap / 2);
                var xNode: Node := new Node(xLabel, x, yNode.index+1);

                var nextNode: Node := yNode.next;
                xNode.previous := yNode;
                xNode.next := nextNode;
                nextNode.previous := xNode;
                yNode.next := xNode;
            }

            omDsSeq := omDsSeq[..yNode.index+1] + [x] + omDsSeq[yNode.index+1..];
            assert tail.previous.index+1 == |omDsSeq|;
            assert omDsSeq[yNode.index+1] == x;

            // TODO:
            // reIndex();
        }

        // Inserts x at the start of the linked list
        method add(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x exists random position in DS
            ensures x in omDsSeq
            modifies head, head.next
        {
            // head.next always not null since it can be tail node in the worst case.
            if(head.next != null) {

                var nextNode: Node := head.next;

                var labelGap: int := nextNode.omLabel - head.omLabel;
                var xLabel: int := head.omLabel + (labelGap / 2);
                var xNode: Node := new Node(xLabel, x, 0);

                xNode.previous := head;
                xNode.next := nextNode;
                nextNode.previous := xNode;
                head.next := xNode;
            }

            omDsSeq := [x] + omDsSeq[..];
            assert tail.previous.index+1 == |omDsSeq|;
            assert omDsSeq[0] == x;

            // TODO:
            // reIndex();
        }

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == (x in omDsSeq)
        {
            exist := false;
            var iNode: Node? := head.next;
            while(iNode != null && iNode != tail)
                invariant iNode == null || (iNode == tail || iNode != tail)
                decreases iNode
            {
                if(iNode.omValue == x) {
                    exist := true;
                    break;
                }

                iNode := iNode.next;
            }

            assert (x in omDsSeq) && exist;
        }

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
        {
            if(xNode.omLabel < yNode.omLabel) {
                isBefore := true;
            } else {
                isBefore := false;
            }
            
            // ghost var xIndex: int := findXIndex(xNode.omValue, head.next);
            // ghost var yIndex: int := findXIndex(yNode.omValue, head.next);
            // assert xIndex < yIndex;
        }

        // function findXIndex(x: int, node: Node?): int
        //     decreases node == null || node.next == tail
        // {
        //     if node == null then -1 else
        //     if node == tail then -1 else
        //     if node.omValue == x then node.index else findXIndex(x, node.next)
        // }

        method append(valSet: set<int>)
            // Check x doesn't exist in DS
            requires exists val :: val in valSet && val !in omDsSeq
            requires oldOmDsSeq == omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + scndSeq && oldOmDsSeq == fstSeq && val in scndSeq && val in valSet
            // Check each value is unique
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        {
            var iValSet := valSet;
            while ( iValSet != {} )
                decreases iValSet;
                modifies tail.previous
            {
                var setVal :| setVal in iValSet;
                
                // tail.previous is head node in the worst case and never be null
                // check whether existing element or not otherwise ignore to keep the uniqueness
                var existSetVal: bool := element(setVal);
                if(tail.previous != null && !existSetVal) {
                    var prevNode: Node := tail.previous;
                    var labelGap: int := tail.omLabel - prevNode.omLabel;

                    if(labelGap == 0) {
                        // TODO:
                        // relabel();
                    }

                    var valLabel: int := prevNode.omLabel + (labelGap / 2);
                    var valNode: Node := new Node(valLabel, setVal, prevNode.index+1);

                    valNode.previous := prevNode;
                    valNode.next := tail;
                    prevNode.next := valNode;
                    tail.previous := valNode;
                }

                omDsSeq := if setVal in omDsSeq then omDsSeq[..] else omDsSeq[..] + [setVal];

                iValSet := iValSet - { setVal };
            }
        }

        method prepend(valSet: set<int>)
            // Check x doesn't exist in DS
            requires exists val :: val in valSet && val !in omDsSeq
            requires oldOmDsSeq == omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x is at the start of the DS always
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + scndSeq && oldOmDsSeq == scndSeq && val in fstSeq && val in valSet
            // Check each value is unique
            ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        {
            var iValSet := valSet;
            while ( iValSet != {} )
                decreases iValSet;
                modifies head.next
            {
                var setVal :| setVal in iValSet;
                
                // head.next is tail node in the worst case and never be null
                // check whether existing element or not otherwise ignore to keep the uniqueness
                var existSetVal: bool := element(setVal);
                if(head.next != null && !existSetVal) {
                    var nextNode: Node := head.next;
                    var labelGap: int := nextNode.omLabel - head.omLabel;

                    if(labelGap == 0) {
                        // TODO:
                        // relabel();
                    }

                    var valLabel: int := head.omLabel + (labelGap / 2);
                    var valNode: Node := new Node(valLabel, setVal, nextNode.index-1);

                    valNode.previous := head;
                    valNode.next := nextNode;
                    nextNode.previous := valNode;
                    head.next := valNode;
                }

                omDsSeq := if setVal in omDsSeq then omDsSeq[..] else [setVal] + omDsSeq[..];

                iValSet := iValSet - { setVal };
            }
        }

        method remove(xNode: Node)
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check each value is unique
            requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
            // Check x doesn't exist in DS
            ensures xNode.omValue !in omDsSeq
        {
            // xNode.next is tail node in the worst case and never be null
            // xNode.previous is head node in the worst case and never be null
            if(xNode.next != null && xNode.previous != null) {
                var nextNode: Node := xNode.next;
                var prevNode: Node := xNode.previous;

                nextNode.previous := prevNode;
                prevNode.next := nextNode;

                // TODO:
                // reIndex();
            }

            omDsSeq := omDsSeq[..xNode.index] + omDsSeq[xNode.index+1..];
        }
    }
    
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