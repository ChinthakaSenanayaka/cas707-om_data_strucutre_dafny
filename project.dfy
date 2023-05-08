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

        // Customized from Dafny MS research https://www.youtube.com/watch?v=kbJO-U9Wp-s
        // Sets are used to decrease since set substraction allows
        ghost var nodeSet: set<Node>;

        constructor (omLbl: int, omVal: int, idx: int)
            ensures omLabel == omLbl && omValue == omVal && index == idx
        {
            new;
            omLabel := omLbl;
            omValue := omVal;

            index := idx;
        }

        ghost predicate isAcyclic()
            reads *
            decreases nodeSet
        {
            this in nodeSet && 
            (next != null ==> next.nodeSet <= nodeSet && this !in next.nodeSet && next.isAcyclic())
        }
    }

    trait OMDataStructTrait {

        ghost var omDsSeq: seq<int>;

        // NOTE: Trait level invariants are not working. Invalid Class/Trait member in Dafny grammar
        // invariant forall fstSeq, scndSeq, val :: omDsSeq == fstSeq + [val] + scndSeq && val !in fstSeq + scndSeq;

        // Check all the values are unique
        ghost predicate checkUnique()
            // NOTE: Weird but try commenting this, neither way is working.
            reads *
        {
            forall i, j :: 0 <= i < j < |omDsSeq| && omDsSeq[i] != omDsSeq[j]
            // forall fstSeq, scndSeq, x :: omDsSeq == fstSeq + [x] + scndSeq && x !in fstSeq + scndSeq
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

        method before(xNode: Node, yNode: Node) returns (isBefore: bool)
            // Checks x and y are different values
            requires xNode.omValue != yNode.omValue
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // If x's position is less than y's position then return true otherwise false
            ensures exists fstSeq, scndSeq :: omDsSeq == fstSeq + [xNode.omValue] + scndSeq && isBefore == (yNode.omValue in scndSeq)

        method append(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check val is at the end of the DS always.
            ensures omDsSeq == old(omDsSeq) + [x]
            // Check all the values are unique. This is an additional check
            ensures checkUnique()

        method prepend(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x is at the start of the DS always
            ensures omDsSeq == [x] + old(omDsSeq)
            // Check all the values are unique. This is an additional check
            ensures checkUnique()

        method remove(xNode: Node)
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x doesn't exist in DS
            ensures xNode.omValue !in omDsSeq

        method getXNode(x: int) returns (node: Node)
            // Check x exists in DS
            requires x in omDsSeq
            ensures node.omValue == x
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

        ghost function getLength(): int
            // NOTE: Doesn't resolve the read access error though error says so.
            // reads tail
            reads *
        {
            if tail.previous == null then 0 else
            if tail.previous == head then 0 else |tail.previous.nodeSet|
        }

        // To be used in decrease clause in while loops
        // NOTE: Nodes can't be used since the recursive call termination by tail node can't be proved.
        ghost function getCurrentLength(node: Node?): int
            requires node == null || node.isAcyclic()
            decreases if node == null then {} else node.nodeSet
            reads *
        {
            if node == null then 0 else
            if node.next == tail then |node.nodeSet| else getCurrentLength(node.next)
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
            
            reIndex();
        }

        method element(x: int) returns (exist: bool)
            // At some position, if x exists then return true otherwise false
            ensures exist == (x in omDsSeq)
        {
            exist := false;
            var iNode: Node? := head.next;
            while(iNode != null && iNode != tail)
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

        method before(xNode: Node, yNode: Node) returns (isBefore: bool)
            // Checks x and y are different values
            requires xNode.omValue != yNode.omValue
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check y exists in DS
            requires yNode.omValue in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // If x's position is less than y's position then return true otherwise false
            ensures exists fstSeq, scndSeq :: omDsSeq == fstSeq + [xNode.omValue] + scndSeq && isBefore == (yNode.omValue in scndSeq)
        {
            if(xNode.omLabel < yNode.omLabel) {
                isBefore := true;
            } else {
                isBefore := false;
            }
            
            ghost var xIndex: int := findXIndex(xNode.omValue, head.next);
            ghost var yIndex: int := findXIndex(yNode.omValue, head.next);
            assert xIndex < yIndex;
        }

        function findXIndex(x: int, node: Node?): int
            decreases node.next == tail
        {
            if node == null then -1 else
            if node == tail then -1 else
            if node.omValue == x then node.index else findXIndex(x, node.next)
        }

        // Source: https://homepage.cs.uiowa.edu/~tinelli/classes/181/Spring11/Tools/Dafny/Examples/square-root.dfy
        method getSqRt(n: int) returns (r : int)
            requires n >= 0;
            // r is the largest non-negative integer whose square is at most n 
            ensures 0 <= r*r && r*r <= n && n < (r+1)*(r+1);
        {
            r := 0 ;
            while ((r+1) * (r+1) <= n)
                invariant r*r <= n ;
            {
                r := r+1 ;
            }
        }

        method append(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check val is at the end of the DS always.
            ensures omDsSeq == old(omDsSeq) + [x]
            // Check all the values are unique. This is an additional check
            ensures checkUnique()
        {
            var prevNode: Node? := tail.previous;
            if(prevNode != null && prevNode != head) {

                var sqrtLbl: int := getSqRt(prevNode.omLabel);
                var tailLbl: int := sqrtLbl * (sqrtLbl + 1);

                var labelGap: int := tailLbl - prevNode.omLabel;

                var xLabel: int := prevNode.omLabel + (labelGap-1 / 2);
                var xNode: Node := new Node(xLabel, x, prevNode.index+1);

                xNode.previous := prevNode;
                xNode.next := tail;
                prevNode.next := xNode;
                tail.previous := xNode;

            } else {
                var xNode: Node := new Node(1, x, 0);

                xNode.previous := head;
                xNode.next := tail;
                head.next := xNode;
                tail.previous := xNode;
            }

            omDsSeq := omDsSeq[..] + [x];
        }

        method prepend(x: int)
            // Check x doesn't exist in DS
            requires x !in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x is at the start of the DS always
            ensures omDsSeq == [x] + old(omDsSeq)
            // Check all the values are unique. This is an additional check
            ensures checkUnique()
        {
            var nextNode: Node? := head.next;
            if(nextNode != null && nextNode != tail) {
                var labelGap: int := nextNode.omLabel - 0;

                var xLabel: int := 0 + (labelGap-1 / 2);
                var xNode: Node := new Node(xLabel, x, 0);

                xNode.previous := head;
                xNode.next := nextNode;
                nextNode.previous := xNode;
                head.next := xNode;

            } else {
                var xNode: Node := new Node(1, x, 0);

                xNode.previous := head;
                xNode.next := tail;
                head.next := xNode;
                tail.previous := xNode;
            }

            omDsSeq := [x] + omDsSeq[..];
        }

        method remove(xNode: Node)
            // Check x exists in DS
            requires xNode.omValue in omDsSeq
            // Check all the values are unique
            requires checkUnique()
            // Check x doesn't exist in DS
            ensures xNode.omValue !in omDsSeq
        {
            var nextNode: Node := xNode.next;
            var prevNode: Node := xNode.previous;

            nextNode.previous := prevNode;
            prevNode.next := nextNode;
                
            reIndex();

            omDsSeq := omDsSeq[..xNode.index] + omDsSeq[xNode.index+1..];
        }

        method getXNode(x: int) returns (node: Node)
            // Check x exists in DS
            requires x in omDsSeq
            ensures node.omValue == x
        {
            var iNode: Node? := head.next;
            while(iNode != null && iNode != tail)
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
    // import c = Collections

    // method main()
    // {
    //     var omDataStruct := new c.OMDataStruct();

    //     // [] - labels | [] - values

    //     omDataStruct.add(4);

    //     // [1] - labels | [4] - values

    //     var node4: c.Node := omDataStruct.getXNode(4);
    //     omDataStruct.addBefore(46, node4);

    //     // [2, 4] - labels | [46, 4] - values

    //     var node46: c.Node := omDataStruct.getXNode(46);
    //     omDataStruct.addAfter(30, node46);

    //     // [2, 3, 4] - labels | [46, 30, 4] - values

    //     omDataStruct.prepend(11);

    //     // [1, 2, 3, 4] - labels | [11, 46, 30, 4] - values

    //     omDataStruct.append(89);

    //     // [5, 10, 15, 20, 25] - labels | [11, 46, 30, 4, 89] - values

    //     var exist30: bool := omDataStruct.element(30);
    //     assert exist30; // true

    //     var exist50: bool := omDataStruct.element(50);
    //     assert !exist50; // false

    //     var isBefore46: bool := omDataStruct.before(node46, node4);
    //     assert isBefore46; // true

    //     var node11: c.Node := omDataStruct.getXNode(11);
    //     var isBefore11: bool := omDataStruct.before(node46, node11);
    //     assert !isBefore11; // false

    //     // [5, 10, 15, 20, 25] - labels | [11, 46, 30, 4, 89] - values

    //     omDataStruct.remove(node4);

    //     // [5, 10, 15, 25] - labels | [11, 46, 30, 89] - values

    //     var exist4: bool := omDataStruct.element(4);
    //     assert !exist4; // false
    // }
}