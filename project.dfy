/**
    om - Order Maintained
    ds - Data Structure
 */
module Collections {
    
    trait INode {
        var omLabel: int;
        var omValue: int;
    }

    class Node extends INode {
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

        ghost var omDsSeq: seq<int>;

        // NOTE: Trait level invariants are not working. Invalid Class/Trait member in Dafny grammar
        // invariant forall fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq;

        // Check all the values are unique
        ghost predicate checkUnique()
        {
            forall fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        }

        method addBefore(x: int, yNode: Node)
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x's position is less than y's position
            ensures exists fstSeq, scndSeq :: old(omDsSeq) == fstSeq + [yNode.omValue] + scndSeq && omDsSeq == fstSeq + [x, yNode.omValue] + scndSeq

        method addAfter(x: int, yNode: Node)
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x's position is greater than y's position
            ensures exists fstSeq, scndSeq :: old(omDsSeq) == fstSeq + [yNode.omValue] + scndSeq && omDsSeq == fstSeq + [yNode.omValue, x] + scndSeq

        // Inserts x at the start of the linked list
        method add(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x exists random position in DS
            ensures x in omDsSeq

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == (x in omDsSeq)

        // method before(xNode: Node, yNode: Node) returns (isBefore: bool)
        //     // Checks x and y are different values
        //     requires xNode.omValue != yNode.omValue
        //     // Check x exists in DS
        //     requires xNode.omValue in omDsSeq
        //     // Check y exists in DS
        //     requires yNode.omValue in omDsSeq
        //     // Check all the values are unique
        //     requires checkUnique()
        //     // If x's position is less than y's position then return true otherwise false
        //     ensures exists fstSeq, scndSeq :: omDsSeq == fstSeq + [xNode.omValue] + scndSeq && isBefore == (yNode.omValue in scndSeq)

        // method append(x: int)
        //     // Check x doesn't exist in DS
        //     requires x !in omDsSeq
        //     // Check all the values are unique
        //     requires checkUnique()
        //     // Check val is at the end of the DS always.
        //     ensures omDsSeq == old(omDsSeq) + x
        //     // Check all the values are unique. This is an additional check
        //     ensures checkUnique()

        // method prepend(x: int)
        //     // Check x doesn't exist in DS
        //     requires x !in omDsSeq
        //     // Check all the values are unique
        //     requires checkUnique()
        //     // Check x is at the start of the DS always
        //     ensures omDsSeq == x + old(omDsSeq)
        //     // Check all the values are unique. This is an additional check
        //     ensures checkUnique()

        // method remove(xNode: Node)
        //     // Check x exists in DS
        //     requires xNode.omValue in omDsSeq
        //     // Check all the values are unique
        //     requires checkUnique()
        //     // Check x doesn't exist in DS
        //     ensures xNode.omValue !in omDsSeq

        // method getXNode(x: int) returns (node: Node)
        //     // Check x exists in DS
        //     requires x in omDsSeq
        //     ensures node.omValue == x
    }

    class OMDataStruct extends OMDataStructTrait {
        var head: Node;
        var tail: Node;

        // NOTE: class level invariants are not working
        // invariant forall fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq;

        constructor ()
        {
            var headNode := new Node(0, 0, 0);
            var tailNode := new Node(0, 0, 0);
            head := headNode;
            tail := tailNode;
            new;
            omDsSeq := [];
        }

        function getLength(): int
        {
            // Just to work aorund previous is Node? nullable
            if tail.previous == null then 0 else
            if tail.previous == head then 0 else tail.previous.index + 1
        }

        // To be used in decrease clause
        function getCurrentLength(node: Node?): int
        {
            if node.next == null then 0 else
            if node.next == tail then 0 else 1 + getCurrentLength(node.next)
        }

        method addBefore(x: int, yNode: Node)
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x's position is less than y's position
            ensures exists fstSeq, scndSeq :: old(omDsSeq) == fstSeq + [yNode.omValue] + scndSeq && omDsSeq == fstSeq + [x, yNode.omValue] + scndSeq
            modifies yNode, yNode.previous
        {
            // yNode.previous always not null since it can be head node in the worst case.
            if(yNode.previous != null) {

                var labelGap: int := yNode.omLabel - yNode.previous.omLabel;
                // TODO: Check xLabel exist or not then relabel
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

            reIndex();
        }

        method addAfter(x: int, yNode: Node)
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x's position is greater than y's position
            ensures exists fstSeq, scndSeq :: old(omDsSeq) == fstSeq + [yNode.omValue] + scndSeq && omDsSeq == fstSeq + [yNode.omValue, x] + scndSeq
        {
            // yNode.next always not null since it can be tail node in the worst case.
            if(yNode.next != null) {

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

            reIndex();
        }

        // Inserts x at the start of the linked list
        method add(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x exists random position in DS
            ensures x in omDsSeq
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
            
            reIndex();
        }

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == (x in omDsSeq)
        {
            exist := false;
            var iNode: Node? := head.next;
            while(iNode != tail)
                decreases getLength() - getCurrentLength(iNode)
            {
                if(iNode.omValue == x) {
                    exist := true;
                    break;
                }

                iNode := iNode.next;
            }

            assert (x in omDsSeq) && exist;
        }

        // method before(xNode: Node, yNode: Node) returns (isBefore: bool)
        //     // Checks x and y are different values
        //     requires xNode.omValue != yNode.omValue
        //     // Check x exists in DS
        //     requires xNode.omValue in omDsSeq
        //     // Check y exists in DS
        //     requires yNode.omValue in omDsSeq
        //     // Check each value is unique
        //     requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        //     // If x's position is less than y's position then return true otherwise false
        //     ensures exists fstSeq, midSeq, scndSeq :: omDsSeq == fstSeq + [xNode.omValue] + midSeq + [yNode.omValue] + scndSeq
        // {
        //     if(xNode.omLabel < yNode.omLabel) {
        //         isBefore := true;
        //     } else {
        //         isBefore := false;
        //     }
            
        //     // ghost var xIndex: int := findXIndex(xNode.omValue, head.next);
        //     // ghost var yIndex: int := findXIndex(yNode.omValue, head.next);
        //     // assert xIndex < yIndex;
        // }

        // // function findXIndex(x: int, node: Node?): int
        // //     decreases node == null || node.next == tail
        // // {
        // //     if node == null then -1 else
        // //     if node == tail then -1 else
        // //     if node.omValue == x then node.index else findXIndex(x, node.next)
        // // }

        // method append(valSet: set<int>)
        //     // Check x doesn't exist in DS
        //     requires exists val :: val in valSet && val !in omDsSeq
        //     requires oldOmDsSeq == omDsSeq
        //     // Check each value is unique
        //     requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        //     // If DS size is 1 then x is at the start of DS or DS size is greater than 1 then x is at the end of the DS.
        //     ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + scndSeq && oldOmDsSeq == fstSeq && val in scndSeq && val in valSet
        //     // Check each value is unique
        //     ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        // {
        //     var iValSet := valSet;
        //     while ( iValSet != {} )
        //         decreases iValSet;
        //         modifies tail.previous
        //     {
        //         var setVal :| setVal in iValSet;
                
        //         // tail.previous is head node in the worst case and never be null
        //         // check whether existing element or not otherwise ignore to keep the uniqueness
        //         var existSetVal: bool := element(setVal);
        //         if(tail.previous != null && !existSetVal) {
        //             var prevNode: Node := tail.previous;
        //             var labelGap: int := tail.omLabel - prevNode.omLabel;

        //             if(labelGap == 0) {
        //                 relabel();
        //             }

        //             var valLabel: int := prevNode.omLabel + (labelGap / 2);
        //             var valNode: Node := new Node(valLabel, setVal, prevNode.index+1);

        //             valNode.previous := prevNode;
        //             valNode.next := tail;
        //             prevNode.next := valNode;
        //             tail.previous := valNode;
        //         }

        //         omDsSeq := if setVal in omDsSeq then omDsSeq[..] else omDsSeq[..] + [setVal];

        //         iValSet := iValSet - { setVal };
        //     }
        // }

        // method prepend(valSet: set<int>)
        //     // Check x doesn't exist in DS
        //     requires exists val :: val in valSet && val !in omDsSeq
        //     requires oldOmDsSeq == omDsSeq
        //     // Check each value is unique
        //     requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        //     // Check x is at the start of the DS always
        //     ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + scndSeq && oldOmDsSeq == scndSeq && val in fstSeq && val in valSet
        //     // Check each value is unique
        //     ensures exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        // {
        //     var iValSet := valSet;
        //     while ( iValSet != {} )
        //         decreases iValSet;
        //         modifies head.next
        //     {
        //         var setVal :| setVal in iValSet;
                
        //         // head.next is tail node in the worst case and never be null
        //         // check whether existing element or not otherwise ignore to keep the uniqueness
        //         var existSetVal: bool := element(setVal);
        //         if(head.next != null && !existSetVal) {
        //             var nextNode: Node := head.next;
        //             var labelGap: int := nextNode.omLabel - head.omLabel;

        //             if(labelGap == 0) {
        //                 relabel();
        //             }

        //             var valLabel: int := head.omLabel + (labelGap / 2);
        //             var valNode: Node := new Node(valLabel, setVal, nextNode.index-1);

        //             valNode.previous := head;
        //             valNode.next := nextNode;
        //             nextNode.previous := valNode;
        //             head.next := valNode;
        //         }

        //         omDsSeq := if setVal in omDsSeq then omDsSeq[..] else [setVal] + omDsSeq[..];

        //         iValSet := iValSet - { setVal };
        //     }
        // }

        // method remove(xNode: Node)
        //     // Check x exists in DS
        //     requires xNode.omValue in omDsSeq
        //     // Check each value is unique
        //     requires exists fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq
        //     // Check x doesn't exist in DS
        //     ensures xNode.omValue !in omDsSeq
        // {
        //     // xNode.next is tail node in the worst case and never be null
        //     // xNode.previous is head node in the worst case and never be null
        //     if(xNode.next != null && xNode.previous != null) {
        //         var nextNode: Node := xNode.next;
        //         var prevNode: Node := xNode.previous;

        //         nextNode.previous := prevNode;
        //         prevNode.next := nextNode;
                
        //         reIndex();
        //     }

        //     omDsSeq := omDsSeq[..xNode.index] + omDsSeq[xNode.index+1..];
        // }

        method getXNode(x: int) returns (node: Node)
            // Check x exists in DS
            requires x in omDsSeq
            ensures node.omValue == x
        {
            var iNode: Node := head.next;
            while(iNode != tail)
                decreases getLength() - getCurrentLength(iNode)
            {
                if(iNode.omValue == x) {
                    node := iNode;
                    break;
                }

                iNode := iNode.next;
            }

            assert iNode.omValue == x && x == node.omValue;
        }

        method reIndex()
        {
            var nextNode: Node? := head.next;
            var index: int := 0;

            while(nextNode != null && nextNode != tail)
                decreases nextNode.next
                modifies nextNode
            {
                nextNode.index := index;
                index := index + 1;
                nextNode := nextNode.next;
            }
        }

        method relabel()
        {
            var index: int := 0;
            var listSize: int := tail.previous.index+1;
            var nextNode: Node? := head.next;

            while(nextNode != null && nextNode != tail)
                decreases nextNode.next
                modifies nextNode
            {
                nextNode.omLabel := listSize * (index + 1);
                nextNode.index := index;
                index := index + 1;
                nextNode := nextNode.next;
            }
        }
    }
    
}

module Runner {
    import c = Collections

    method main()
    {
        var omDataStruct := new c.OMDataStruct();

        // [] - labels | [] - values

        omDataStruct.add(4);

        // [1] - labels | [4] - values

        var node4: c.Node := omDataStruct.getXNode(4);
        omDataStruct.addBefore(46, node4);

        // [2, 4] - labels | [46, 4] - values

        var node46: c.Node := omDataStruct.getXNode(46);
        omDataStruct.addAfter(30, node46);

        // [3, 6, 9] - labels | [46, 30, 4] - values

        var prependValSet: set<int> := {11};
        omDataStruct.prepend(prependValSet);

        // [4, 8, 12, 16] - labels | [11, 46, 30, 4] - values

        var appendValSet: set<int> := {89};
        omDataStruct.append(appendValSet);

        // [5, 10, 15, 20, 25] - labels | [11, 46, 30, 4, 89] - values

        var exist30: bool := omDataStruct.element(30);
        assert exist30; // true

        var exist50: bool := omDataStruct.element(50);
        assert !exist50; // false

        var isBefore46: bool := omDataStruct.before(node46, node4);
        assert isBefore46; // true

        var node11: c.Node := omDataStruct.getXNode(11);
        var isBefore11: bool := omDataStruct.before(node46, node11);
        assert !isBefore11; // false

        // [5, 10, 15, 20, 25] - labels | [11, 46, 30, 4, 89] - values

        omDataStruct.remove(node4);

        // [4, 8, 12, 16] - labels | [11, 46, 30, 89] - values

        var exist4: bool := omDataStruct.element(4);
        assert !exist4; // false
    }
}