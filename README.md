# Feup MFES Summary (Alloy only)
```als
all exercise : Mfes.alloy | some exercise in Repo and no exercise.responsibility & Me.responsibilities
```
	
 1. [Execute custom examples](#custom-examples)
 1. [Alloy4fun Exercises](#alloy4fun-exercises)
## Custom examples
1. Considerando as relações A e B indique o valor das expressões em Alloy:

`A = {(a0,d0), (b0,a0), (b1,c1),(d0,d4),(d4,b1) }`
 * a. {(a0),(b1)} <: A
 * b. {(a0)}.^A 

```alloy
enum A {A0}
enum B {B0, B1}
enum C {C1}
enum D {D0, D4}

sig Rel {
    r: (A+B+C+D)->(A+B+C+D)
} {
    r = {A0->D0 + B0->A0 + B1->C1 + D0->D4 + D4->B1}
}

run { }
```
Depois `execute`, na janela de execution ver a tab `evaluator` e escrever lá o query, por exemplo: `{A0 + D0} <: Rel.r`

## Alloy4fun Exercises

### 1 http://alloy4fun.di.uminho.pt/3cy7jaB4ESqdb2txK

```als
//A student must be enrolled in one or more courses
sig Course{}
sig Student{ enrolledin : set Course}
// write a predicate Quizz to verify that
pred Quizz{
    // "a student must be enrolled in one or more courses"	
    all s: Student | #(s.enrolledin) > 0 // or some s.enrolledin
}
```
### 2 http://alloy4fun.di.uminho.pt/a3CyrvrbWHAdtE2x4

```als
sig Employee{}
sig Department{}
one sig Company {
    isDirectorOf: Employee -> Department
}
// write a prediate Quizz to check that
pred Quizz {
    // In a company, each department has exactly one director (chosen among 
    // the company's employees), but each employee can only be the director 
    // of at most one department
    all d: Department | one  Company.isDirectorOf.d 
    all e: Employee   | lone Company.isDirectorOf[e]
}
```

### 3 http://alloy4fun.di.uminho.pt/2zrpuc2wg4gsCaY63

```als
sig researchUnit {}
sig researcher { 
    collaborate: set researchUnit,
    affiliated: set researchUnit
}
// Write a predicate Quizz to check that
pred Quizz {
    // A researcher may collaborate with multiple research units (one or more),
    // but must be affiliated with just one research units.
    all r: researcher | some collaborate[r] and one affiliated[r]
}   
```

### 4 http://alloy4fun.di.uminho.pt/6pc5KQzjhozDkNgPv

```als
abstract sig Person {}
sig Teacher extends Person {}
abstract sig Student extends Person {}
sig Graduate, Undergrad extends Student {}
sig Instructor in Teacher + Graduate {}
sig Course {
    taughtby: one Instructor,
    enrolled: some Student
}
// write a predicate to check that
pred Quizz {
    // "the instructor of a course cannot be enrolled in such course"  
    all c:Course | c.taughtby not in c.enrolled
}
```

### 5 http://alloy4fun.di.uminho.pt/QM77ku4rGxTMeK9oG

```als
abstract sig Person {}
sig Teacher extends Person {}
abstract sig Student extends Person {
    courses: set Course
}
sig Graduate, Undergrad extends Student {}
sig Instructor in Teacher + Graduate {}
sig Course {
    taughtby: one Instructor, 
    enrolled: some Student 
}
// Write a predicate Quizz to check that
pred Quizz {
    // the relationships courses and enrolled must be consistent, i.e., 
    // if a student has a Course, that Course must be enrolled by the Student  
    // and vice-versa
    courses = ~enrolled
    // or, with a locally defined variable
    // let x = (courses & ~enrolled) | courses = x and enrolled = ~x
}
```

### 6 http://alloy4fun.di.uminho.pt/aSPhAXu7aXWu9FeD6

```als
open util/ordering[Time]
// Consider the following model of a mobile phone
sig Number {}
// A simple model of Time as a total order
sig Time {}
one sig Now in Time {}
// Each contact can have several phone numbers
sig Contact {
    phones : some Number
}
// Each call is to a particular phone number at a particular time
sig Call {
    number : one Number,
    time : one Time
}
// You can check their correctness with the different commands and
// specifying a given invariant you can assume the others to be true.
pred Inv1 {// A phone number cannot belong to two different contacts
    all disj c1,c2:Contact | no (c1.phones & c2.phones)
    // or
    all n : Number | lone phones.n
}
pred Inv2 {// Every called number belongs to a contact
    Call.number in Contact.phones
}
pred Inv3 {// Simultaneous calls cannot exist
    all disj c1,c2: Call | c1.time != c2.time
}
pred Inv4 {// All calls were made in the past
    all c: Call | c.time in prevs[Now]
}
```

### 7 http://alloy4fun.di.uminho.pt/xe9fdhwqCqKgChxbx

```als
// Consider the following model for courses where students work in teams
sig Student {}
sig Team {
    members : some Student
}
sig Grade {}
sig Course {
    enrolled : set Student,
    teams : set Team,
    grade : Student -> lone Grade
}
pred Inv1 {// Each student must be enrolled in at least one course
    no s :Student | s not in Course.enrolled
}
pred Inv2 {// All the members of a team are enrolled in the respective courses
    all c : Course | c.teams.members in c.enrolled
}
pred Inv3 {// Only enrolled students can have a grade in a course
    all c : Course | c.grade.Grade in c.enrolled
}
pred Inv4 {// Each student enrolled in a course belongs to exactly one of its teams
    all c : Course | all s : c.enrolled | one c.teams & members.s
	//all c : Course , s : c.enrolled | one c.teams & members.s
}
pred Inv5 {// All members of a team that already have been graded have the same grade
    all c : Course | all s1, s2 : c.enrolled | c.teams & members.s1 = c.teams & members.s2
        and s1+s2 in c.grade.Grade => c.grade[s1] = c.grade[s2]
}
```

### 8 http://alloy4fun.di.uminho.pt/EvHauGwoERQ3HHGfc

```als
open util/ordering[Addr]
sig Addr {// A memory address can be allocated to a memory block
    allocated : lone Block
}
sig Free in Addr {}// The free memory addresses
sig Block {// Each allocated memory block has a pointer
    pointer : one Addr
}
pred Inv1 {// Each memory address is either free or allocated to a block
    all a : Addr | (a in Free and no a.allocated) or (a not in Free and one a.allocated)
}
pred Inv2 {// A block pointer is one of its allocated addresses
    all b : Block | all a : Addr | b->a in pointer => a.allocated = b
}
pred Inv3 {// All memory addresses allocated to a block are contiguous 
    all b : Block | #allocated.b>1 => all a1 : allocated.b | 
    one a2 : allocated.b - a1 | a2 = next[a1] or a2 = prev[a1]
}
pred Inv4 {// The pointer to a block is smaller then all its allocated addresses
    all b : Block | all a: allocated.b - b.pointer | lt[b.pointer, a]
}
```

### 9 http://alloy4fun.di.uminho.pt/ri2bbMKEkonsY66v3

```als
// Consider the following model of an online auction system
sig Product {}
sig Bid {}
sig Auction {
    product : one Product
}
sig User {
    auctions : set Auction,
    bids : Auction -> Bid
}
pred Inv1 {// Every auction belongs to a user
    Auction = User.auctions
}
pred Inv2 { // A user cannot bid on its own auctions
    all u : User | no u.bids.Bid & u.auctions
}
pred Inv3 {// All the bids in an auction are different
    #bids = #User.bids
}
```

### 10 http://alloy4fun.di.uminho.pt/g8dYNQd3ys3MjbHoL

```als
// Consider the following simplified model of Java classes
sig Class {
    super : lone Class, 
    vars : set Var
}
one sig Object extends Class {}
sig Name {}
sig Var {
    name : one Name
}
pred Inv1 {// The object class has no instance variables
    no Object.vars
}
pred Inv2 {// All classes except Object have a superclass
    all c : Class-Object | one c.super
}
pred Inv3 {// A class cannot declare two instance variables with the same name
    all c: Class | all disj v1,v2 : c.vars | v1.name!=v2.name
}
pred Inv4 {// A class cannot inherit from itself
    all c : Class | no c & c.^super
}
```

### 11 http://alloy4fun.di.uminho.pt/6umZreF5bnTXmWeTD

```als
open util/ordering[Decision]
// Consider the following model of an academic publisher reviewing system
sig Person {}
abstract sig Decision {}
one sig Reject,Borderline,Accept extends Decision {}
fact {
    Reject.next = Borderline
    Borderline.next = Accept
}
sig Article {
    authors : some Person,
    reviews : Person -> Decision
}
sig Accepted in Article {}
pred Inv1 {// Each article has at most one review by each person
    all a : Article | #a.reviews = #a.reviews.Decision
}
pred Inv2 {// An article cannot be reviewed by its authors
    all a : Article | no a.authors & a.reviews.Decision
}
pred Inv3 {// All accepted articles must have at least one review
    all a : Accepted | some a.reviews
}
pred Inv4 {// All articles with an Accept decision are automatically accepted
    all a : Article | some a.reviews.Accept => a in Accepted
}
```

### 12 http://alloy4fun.di.uminho.pt/xoJz9NfK4o8Gs2eDH

```als
open util/ordering[Position]
// Consider the following model of an automated production line
// The production line consists of several positions in sequence
sig Position {}
// Products are either components assembled in the production line or 
// other resources (e.g. pre-assembled products or base materials)
sig Product {}
// Components are assembled in a given position from other parts
sig Component extends Product {
	parts : set Product,
	position : one Position
}
sig Resource extends Product {}
sig Robot {// Robots work somewhere in the production line
    position : one Position
}
pred Inv1 {// A component requires at least one part
    all c : Component | some c.parts
}
pred Inv2 {// A component cannot be a part of itself
    all c : Component | c not in c.^parts 
}
pred Inv3 {// The position where a component is assembled must have at least one robot
    Component.position in Robot.position
}
pred Inv4 {// The parts required by a component cannot be assembled at a later position
    all c : Component | all p : c.^parts & Component | gte[c.position,p.position]
}
```

### 13 http://alloy4fun.di.uminho.pt/4KYLfsxtvCNJThFpp
#### This one is unclear about "what" the same work means, but `Inv4` is correct, so deduce it :)

```als
/* Consider the following model of an online CV platform that allows a
profile to be updated not only by its owner but also by external institutions,
to certify that the user indeed has produced certain works. 
Works must have some unique global identifiers, that are used to
clarify if two works are in fact the same.
*/
abstract sig Source {}
sig User extends Source {
    profile : set Work,
    visible : set Work
}
sig Institution extends Source {}
sig Id {}
sig Work {
    ids : some Id,
    source : one Source
}
pred Inv1 {
    all u : User | u.visible in u.profile
}
pred Inv2 {// A user profile can only have works added by himself or some external institution
    all u : User | all w : u.profile | w.source in u + Institution
}
pred Inv3 {// The works added to a profile by a given source cannot have common identifiers
    all u : User | all disj w1, w2 : u.profile | w1.source = w2.source => no w1.ids & w2.ids
}
pred Inv4 {// The profile of a user cannot have two visible versions of the same work
    all u : User | all disj w1, w2 : u.visible | w1 not in w2.^(ids.~ids)
}
```

### 14 http://alloy4fun.di.uminho.pt/i5mpZsgf2YarYyepy

```als
// A graph can be modeled using a set Node containing all nodes and
// a binary relation Edge containing all the edges.
// Using relational logic specify contraints that characterize the following
// particular types of graphs
pred Dag {
    // a direct acyclic graph
    all n : Node | n not in n.^Edge
}
pred Ring {
    // The graph is a single ring, with edges pointing to successors
    all n : Node | Node = n.^Edge and #Edge = #Node
}
pred Tree {
    // The graph is a single tree, with edges pointing to parents
    one n : Node | no n.Edge and all n1 : Node-n | n in n1.^Edge and one n1.Edge
}
```

### 15 http://alloy4fun.di.uminho.pt/HHqxbmmCu2iN9zNtF

```als
sig Person{}
sig Man in Person{}
sig Woman in Person{}

//write a predicate Quizz to check that 
pred Quizz {
    // A person must be a man or a woman
    // A Person cannot be simultaneous man and woman
    Man + Woman = Person
    no Man & Woman
}
```

### 16 http://alloy4fun.di.uminho.pt/BAAEJo6RM2e2GcRZt

```als
//consider a simplifyed specification of a Graph 
// with arrows between Points
sig Point {}
sig Graph{
    edge: Point -> some Point
}
// build a predicate Insere
pred Insere[g:Graph,p1: Point, p2:Point,g':Graph] {
    // that inserts an arrow in a Graph g and returns the result in a Graph g'
    g'.edge = g.edge ++ p1->(g.edge[p1] + p2)
}
```

### 17 http://alloy4fun.di.uminho.pt/5jabBMzWjWnBeFb64

```als
sig Point {
    edge : some Point 
}
// build a predicate biconnected
pred biconnected {
/* that checks if a Graph is biconnected. A biconnected graph is a connected
and "nonseparable" graph, meaning that if any one vertex were to be removed, 
the graph will remain connected. Therefore a biconnected graph has no articulation 
vertices  */
    all p0 : Point, disj p1,p2 : (e.Point + e[Point] - p0) | p1 in p2.^remedge[edge, p0]
}
fun remedge [ e: edge, p0:Point] : set edge{
    e - p0->Point - Point->p0
}
```

