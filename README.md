[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-22041afd0340ce965d47ae6ef1cefeee28c7c493a6346c4f15d667ab976d596c.svg)](https://classroom.github.com/a/dPwN1w3S)
# Final project

**Explain the general theme and specific features of your project.**
- The general theme & specific features of our project is given a linked list, to prove whether it
- is circular or not using Floyd's cycle specifically. We defined what it entails to be circular list via a path & lookup
- definition where each node in a linked list (contained via a vec) holds data (arbitrary) and a pointer to the next node (maybe).
- If it does not contain a pointer to the next, then the next value is nothing in which case that node could not be a part of an
- infinitely repeating circular linked list.
- We tried defining an absurdPath type to fill-in holes where the path could not result in a circular linked list. However, we ran
- into some trouble with the zero case as that was something that needed to be proven for an absurdPath. However, we could not touch
- the zero case as after some changes to our project, we implicitly defined the n as suc n to get rid of meta-variables that were
- causing issues with our proofs. Note, though, that the absurdPath proof would still suffice to fill the holes.
- We also struggled with defining the floyd case to recurse in due to Paths not equating. We tried pattern matching to our 2 cases
- of zero and suc for paths, but were getting stuck with a path we did not define.

- Our Floyd's algorithm follows the implementation of traversal of a rabbit & tortoise. The rabbit node (fast) moves every 2 nodes each turn,
- and the tortoise (slow) moves 1 node each turn. The base cases are if the rabbit & tortoise's next are equal (meaning that they are at the same
- node). This implies that the rabbit caught the tortoise, meaning that it had to have gone in a loop, identifying that the linked-list is \
- circular. The other 2 cases are where the rabbit or the tortoise arrive at a node who's next is nothing. This implies the list is not circular
- and terminates the program by giving a decidability of no on the circular type. We used equality and a stepping function to traverse the list
- and to evaluate in each step.


**Cite any resources or existing code you used.**
- We used Vec, Fin, Nat, Maybe, and the ordering from the standard library. Note that the ordering & compare was copied from the std lib because the code
- would not import properly, but we did cite the hyperlink to the ordering datatype.
- We asked ChatGPT how to do a with for multiple functions as well as how to go about a non-circular proof. It recommended proving that a path could be
- absurd. We asked for it to broadly outline what we would need to prove, specifying not to give us specific code. Overall, the outline was helpful for
- structuring, and we believe we are close to a complete absurdPath function.


**Discuss any challenges, or anything you'd like feedback on.**
- A big challenge was that we had to change our circular definition to take 2 paths (one from zero and another going from i to i) to prove our
- Floyd cycle algorithm. This was a substantial hinderance as we had previously written our main floyd algorithm as well as all other cases to
- fit the case with just 1 path. Thus, we had to start over on most of our functions on the last day. It is worth noting that we did get to
- edge cases in the original proof with one path in which FloydEq would have to recurse again.
- The algorithm would have originally worked, but we wouldn't be able to save the information necessary to prove a loop. The second time, we
- were saving the necessary information, but could not get the algorithm to work.

- Specifically to functions, we were unable to complete the absurdPath. It was meant to output an absurdity on the nothing case, but was trying
- to match to a zero case instead, so it was unsolvable due to how we setup the zero case. We tried making helpers to get the node as well as
- to prove/derive by the contradiction.

- We also tried to fill in the primary holes for floyd with the newer method but were not able to due to Path goals appearing that we did not
- define. For the helper, we got the first case working. We commented out some code taht was working accept for an odd inject error. We left in
- the incomplete one with the equality case uncommented so that you could see at least one case.
- As for the stepping functions, we believe that they are written correctly; we simply struggled to get the pattern matching to align with the
- "injecting" complaint received.

- We would definitely like to see feedback on how to fill in any holes, but especially absurdPath, the cases for the floydhelper', and the cases
- for the recursive case in floyd. Overall, this was a very educational project. We wish that we were able to finish, but sometimes incomplete definitions
- initially can lead to practically restarting the entire project. 


