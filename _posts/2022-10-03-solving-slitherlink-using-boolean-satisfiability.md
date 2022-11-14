---
title: Solving Slitherlink Using Boolean Satisifiability
date: 2022-10-03 00:00:00 +0530
categories: [SAT/SMT Solver, Slitherlink]
tags: [boolean satisfiability, propositional logic, SMT/SAT Solvers, slitherlink]
toc: true
math: true
pin: true
---

## What is Slitherlink?

Slitherlink is a Japanese Puzzle Game I love. I'd made a video explaining it a year ago, you can check it out if you don't know about the game. (I apologise for my voice in advance, I was half asleep)

<iframe src="https://www.youtube.com/embed/EMuvNXjdWEE" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

## Why this Project Means so Much to me

> Feel Free to skip this
>
> {: .prompt-info}

A few years ago I had bought a book[^Puzzle Ninja] filled with Japanese Puzzles. The first Puzzle introduced in the book and arguably my favourite - alongside KenKen - was Slitherlink.

Coming to September of 2021, while Solving Slitherlink Puzzles, I had the urge to make a solver for it. When I asked [Jinen](https://jinensetpal.github.io/) for help with it.

![JinenSS](JinenSS.png)

This project took a long time to complete and while others exaggerate the hours activities took on their CommonApp, I may have understated this one out of sheer embarassment at how long it took. Arguably I didn't spend much time on it at a go since something or the other always came up. Most of the time spent on this project was spent going on tangents as I learned new things while coming up with a way to approach this project. It would take too long to list what all I learned through this project so I shall skip it for now. 

In March of 2022, one night I suddenly got the motivaiton to complete the project and managed to do most of it until a horrible bug stopped me. I spent **hours** trying to fix this bug, even had a 2 hours long zoom session with Jinen to help me find the bug, but our efforts were futile.

Finally in June of 2022 after my internships ended and I got COVID, I decided to start this project again... from scratch. In doing so, I found the bug, the most ridiculous thing possible: a simple algebra mistake while writing the algorithm.

Unfortunately, since school had restarted and COVID had trained all my energy I sat down to complete the project again finished it in July.

![JinenSS](JinenS2.png)

This project took wayyy longer than it should have but the lessons learned and the skills acquired make it worth it. Working on my own, this project taught me how to teach myself new concepts and how to apply them.

I would like to thank Jinen for motivating me to complete this project and would like to formally apologise for that 2 hour debugging session that was to no avail. I would also express my gratitude to Alka Ma'am, my Computers Teacher who taught me Propositonal Logic, without which even the thought of learnig about SAT Solvers would have scared me.

## El Código

Before I start explaining my project, here is the code. It's also on my [GitHub](https://github.com/siddkhera) !

I apologise if the code is succint to the point where it's ugly. I had a goal of writing an effecient solver that could be printed out in less than one page(from the emacs buffer). Alka Ma'am and Jinen would be able to attest that code this ugly could only have been written by me.

```python
import pycosat
from csv import reader
from itertools import combinations

with open('slitherlink.csv', 'r') as read_obj:
    csv_reader = reader(read_obj)
    squares = list(csv_reader)

rows=len(squares) #No. of Rows
cols=len(squares[0]) #No. of Coloumns

def LineID(x,y,horizontal):
    return ((0<=x<=rows and 0<=y<cols) and ((x*cols)+y+1)) if horizontal else ((0<=x<rows and 0<=y<=cols) and cols*(rows+x+1)+x+y+1)

def linesAround(x,y,horizontal,pre):
    return list(filter((False).__ne__, ([LineID(x,y,False), LineID(x-1,y,False), LineID(x,y-1,True)] if pre else [LineID(x,y+1,False), LineID(x-1,y+1,False), LineID(x,y+1,True)]) if horizontal else ([LineID(x,y-1,True), LineID(x,y,True), LineID(x-1,y,False)] if pre else [LineID(x+1,y-1,True), LineID(x+1,y,True), LineID(x+1,y,False)])))

def nTrue(vars,n):
    return list(map(lambda x:list(x),list(combinations([-i for i in vars],n+1))))+list(map(lambda x:list(x),list(combinations(vars,len(vars)+1-n))))

def aroundSquare(x,y):
    return [LineID(x,y,True),LineID(x,y,False),LineID(x+1,y,True),LineID(x,y+1,False)]

cnf=[]

for i in list(range(rows+1)):
    for j in list(range(cols+1)):
        cnf+=nTrue(aroundSquare(i,j),int(squares[i][j])) if (i<rows and j<cols and squares[i][j]!='.') else []
        for hori in [True,False]:
            for t in [True,False]:
                cnf+=[k+[-lineId(i,j,hori)] for k in nTrue(linesAround(i,j,hori,t),1)] if ((not hori or j<cols) and (hori or i<rows)) else []

def IDtoCoord(num):
    if num>(rows+1)*cols:
        num-=1+(rows+1)*cols
        return linesAround(num//(cols+1),num%(cols+1),False,True)+linesAround(num//(cols+1),num%(cols+1),False,False)
    else:
        num-=1
        return linesAround(num//(cols),num%(cols),True,True)+linesAround(num//(cols),num%(cols),True,False)

def ExtraLoops(TrueLines,LinesNotTravelled):
    while(LinesNotTravelled!=[]):
        TrueLines.remove(LinesNotTravelled[0])
        LinesNotTravelled=[i for i in IDtoCoord(LinesNotTravelled[0]) if (i in TrueLines)]
    return TrueLines

for sol in pycosat.itersolve(cnf):
    TrueLines=[i for i in sol if i>0]
    LoopsRemaining=ExtraLoops(TrueLines,[TrueLines[0]])
    if LoopsRemaining==[]:
        print(sol)
```

## Backtracking and Soduku Solvers

Many people have created solvers for the (more) popular Japanese Puzzle - Sudoku. Almost all of these solvers use a method known as backtracking, like the one on this [video](https://www.youtube.com/watch?v=G_UYXzGuqvM). If I had used a similar backtracking uproach on Slitherlink, the puzzles would have taken extremely long. (Technically I still used it but through the DPLL algorithm that was implemented in the SAT Solver)

To put it simply, backtracking is simply making guesses and going back and changing the guess if it doesn't work. 

We iterate through all the possible guesses until we find one that works.

```
Initialise grid with all lines neither present not absent
Optimise and apply concrete rules shown in video?

function Check(Position, Absent or Present)
  return true if guess is valid
 
function Solve()
  iterate through the lines in the grid marked as neither Absent nor Present
  	for x in Present, Absent
	  	if Check(Postion, Line x)
  			Mark Line on this grid as x
  			Solve()
  			Mark Line on grid as neither Present nor Absent
  	terminate this instance of the function
```

At the end if there remain lines on the grid marked as neither Absent nor Present, the puzzle is not solvable. Initially the Slitherlink Solver was going to look like this but I decided  against since this method is extremely slow and gets exponentially slower as the puzzle gets bigger. Even if I had added optmisations to this puzzle by trying to apply the rules I have mentioned in the video above, it would still have been terribly inefficient. Luckily I found another method, one that involves Boolean Satisfiability. (Two research papers that helped me greatly 1[^paper1] and 2[^paper2]) The second one 

## P vs NP and NP Completeness

***If you're getting confused, [forget about it](https://www.youtube.com/watch?v=pS6zJ7IsJkM)***

I tried consicely explaining P vs NP. I'll perhaps make another post explaining the intricacies of P vs NP.

What I'm going to explain will skip over a lot of intricacies of the definition such as $$P\subseteq NP$$ or that we don't know if $$P=NP$$

P problems are those which are both easy to check and solve. NP problems are easy to check and hard to solve. NP complete problems are problems in NP such that they can simulate every problem in NP. Or that every problem in NP can be represented as/reduced to an NP complete problem.

For those familiar with Big O notation, P problems are solvable in polynomial time by a deterministic Turing Machine $$O(n^c)$$ for a constant $c$ whereas problems in NP take exponentially longer to solve as the numbe of variables gets larger $$O(x^n)$$. I'm skipping over a lot of important nuances, for which I will make a new post.

[Simplest video explaining P vs NP I could find ](https://www.youtube.com/watch?v=YX40hbAHx3s)

[ A Video by Proffesor Moshe Vardi explaining P vs NP in more detail ](https://www.youtube.com/watch?v=7jZ2yha4nH8)

## Boolean Satisfiability

I decided not to directly use backtracking and instead use a SAT Solver. (Even the SAT Solver uses backtracking).

Boolean Satisfiability is an example of this really hard NP complete problem such that other hard problems like Slitherlink can be converted to it. Slitherlink was also proven to be NP Complete[^PROOF].

SAT Solvers are ridiculously fast at solving these hard problems because humans have optimised them to a great degree. I convert the problem of Slitherlink into a problem of Boolean Satisfiability 

#### Well what is Boolean Satisfiability

Boolean Satisfiability or SAT is the first problem to have been proven to be NP Complete. Boolean Satisfiability is tells us whether a Boolean Formula is satisfiable or not. I don't have the patience to explain what Boolean Formulas are so I will give an example of Boolean Formula in CNF as required by the SAT Solver.

Let A represent that I'm hungry, this statement can either be true or false

Let B represent that I'm sad, this statement can either be true of false as well

All these need to be true

**(I'm hungry or I'm sad) and (I'm hungry or I'm not sad) and (I'm not hungry or I'm sad)**

The SAT Solver will tell me that this statement can be satisfied if I'm both hungry and sad

This statement can be represented as

$$(A\lor B)\land (A\lor \neg B) \land (\neg A\lor B)$$

Where $$\lor ,\land ,\neg$$ represent or, and, not respectively.



$$(A\lor B)\land (A\lor \neg B) \land (\neg A\lor B) \land (\neg A\lor \neg B)$$

The SAT Solver will tell us that this statement is UNSAT(Unsatisfiable)

If A is true and B is true then $$(\neg A\lor \neg B)$$ is false

If A is true and B is false then $$(\neg A\lor B)$$ is false

If A is false and B is true then $$( A\lor \neg B)$$ is false

If A is false and B is false then $$(A\lor B)$$ is false

This statement cannot ever be true, therefore it is unsatisfiable.

Now that I've explained the basics of what is needed to understand the code, I can start explaining the code

## Defining the Puzzle

```python
with open('slitherlink.csv', 'r') as read_obj:
    csv_reader = reader(read_obj)
    squares = list(csv_reader)
```

We take the slitherlink grid as a .csv file where the numbers on the grid represent the numbers on the slitherlink grid and ''.' used to represent blank squares. This grid is then represented as a 2D grid in python: `squares`.

The squares are given coordinates as shown, they are the standard way 2D grids are represented in code with indexing starting from 0.

$$Square\ Coordinater: Square_{x,y} \to (x,y) \in \{0,...,rows - 1 \} \times \{0,...,cols-1 \}$$

We will asign a unique ID to every line, they will act as variables for the CNF. These IDs will be integers but should be not thought of as numbers, they're simply variables. Using integers is far more convenient. In the above example we have used $$A\ and\ B$$, here we would be using non zero positive integers.

The lines around the squares are represented as showns below.

```python
rows=len(squares) #No. of Rows
cols=len(squares[0]) #No. of Coloumns

def LineID(x,y,horizontal):
    return ((0<=x<=rows and 0<=y<cols) and ((x*cols)+y+1)) if horizontal else ((0<=x<rows and 0<=y<=cols) and cols*(rows+x+1)+x+y+1)
```

We are going to assign a unique non zero integer id to every line on the Slitherlink board. The numbers start with the horizontal lines, and go on to the vertical ones. We will define a function to convert a horizontal or vertical line with coordinates to it's unique id. We will use a simple coordinate system to keep track of the lines $$Horizontal\ Lines: h_{x,y} \to (x,y) \in \{0,...,rows \} \times \{0,...,cols-1 \}$$ and $$Vertical\ Lines: v_{x,y} \to (x,y) \in \{0,...,rows-1 \} \times \{0,...,cols \}$$ but will also assign them a unique positive integer to identify them. The number start from 1 since SAT solvers don't accept 0 as a variable, $$h_{0,0}$$ is represented as 1. Above we have used A and B to represent variables that give true or false, here we are using numbers. If 1 is true that means that the first horizontal line is drawn in the Slitherlink puzzle and so on.

![GridCood](SlitherID.jpeg)

Generally, we can represent the horizontal line $$h_{x,y}$$ as $$(x \times (cols))+(y+1)$$, the last horizontal line at $h_{rows,cols-1}$ will be the $(rows+1) \times cols$ this is rather obvious, but can help us verify the formula. We can put in $x=rows$ and $y=cols-1$, we get $$(rows \times (cols))+(cols-1+1)=rows \times cols + cols = (rows+1) \times cols$$

The vertical lines start from after the horizontal lines, therefore the first vertical line, $$v_{0,0}$$ is given the id $$(rows+1) \times cols + 1$$. Let's forget about the fact that the ids for vertical lines start after horizontal lines, and simply give the vertical lines ids with $$v_{0,0}$$ as 1,  $$v_{0,1}$$ as 2 and so on, uptil the last vertical line at $$v_{rows-1,cols}$$ which will get the value of $$rows \times (cols+1)$$. We can use a modification of the formula used for horizontal lines. $$v_{x,y}=x \times (cols+1) +y+1$$.

We can simply add the number of horizontal lines to this formula to give us a unique id for every line, since the ids for vertical lines start after horizontal lines. Therefore the id for vertical lines can be given by

$$ v_{x,y} = (rows+1) \times cols + x \times (cols + 1) + y + 1 = cols\times (rows + x + 1) + x + y + 1 $$

As mentioned before, we can get the id of horizontal lines with

$$ h_{x,y} = x \times cols + y + 1$$

The `LineID()` function gives us the Line ID of a line if we're given its x and y coordinates. If the x and y values are not within the suitable range, it returns a `False`. It only returns a true if the values given are within the suitable range.

![GridCood](SlitherCood.jpeg)


## Rules of Slitherlink

There are 3 rules for Slitherlink as I've mentioned in the video above

1. Single Loop
2. Numbers in a Cell
3. Loop never crosses itself

We enfore Rules 2 and 3 in the CNF we give to the SAT solver and then iterate over all the given solutions to find one that follows Rule 1.

These Rules have been explained in my video linked above.

## Lines around a Cell/Another Line

#### Lines Around a Line

```python
def linesAround(x,y,horizontal,pre):
    return list(filter((False).__ne__, ([LineID(x,y,False), LineID(x-1,y,False), LineID(x,y-1,True)] if pre else [LineID(x,y+1,False), LineID(x-1,y+1,False), LineID(x,y+1,True)]) if horizontal else ([LineID(x,y-1,True), LineID(x,y,True), LineID(x-1,y,False)] if pre else [LineID(x+1,y-1,True), LineID(x+1,y,True), LineID(x+1,y,False)])))
```

This is the longest line of code in the program and should have been broken into multiple if statements but I made it just one line to reduce the number of lines of code.

This 'line' of code gives the number of lines around a line. In order to make the code succinct, it has become difficult to understand, so I shall break it down.

Since the `LineID()` function gives us False in the event that a line does not exist in that position. `list(filter((False).__ne__, (l)` filters all the false values from the list l. We use this to filer all the values we get as `False`.

There are 4 possibilities of lines around a line we need to find. The line can either be horizontal or vertical. Each line has two points, with different lines connected to each of them. `linesAround(x,y,horizontal,pre)` x and y represent the x and y coordinates; horizontal refers to whether or not the line is vertical or horizontal like the last function (True=Horizontal, False=Vertical); pre refers to the anterior point of the line (left point in horizontal lines and upper point in vertical lines).

![Hori](LineALineH.jpg)
![Verti](LineALineV.jpg)

For each of the 4 possibilites, the lines around the point can be represented as 

1. Let the line be a Horizontal Lines with coordinates $$\alpha ,\beta$$ such that we need to find the points attached to its anterior (left) point. They can be represented as 

$$ (\alpha ,\beta, Vertical),(\alpha -1,\beta, Vertical)\ and\ (\alpha, \beta -1, Horizontal)$$

2. Let the line be a Horizontal Lines with coordinates $$\alpha ,\beta$$ such that we need to find the points attached to its posterior (right) point. They can be represented as 

$$ (\alpha ,\beta + 1, Vertical),(\alpha - 1,\beta + 1, Vertical)\ and\ (\alpha, \beta + 1, Horizontal)$$

3. Let the line be a Vertical Lines with coordinates $$\alpha ,\beta$$ such that we need to find the points attached to its anterior (left) point. They can be represented as 

$$ (\alpha ,\beta - 1 , Horizontal),(\alpha,\beta, Horizontal)\ and\ (\alpha - 1, \beta, Vertical)$$

4. Let the line be a Vertical Lines with coordinates $$\alpha ,\beta$$ such that we need to find the points attached to its posterior (right) point. They can be represented as 

$$ (\alpha + 1,\beta - 1, Horizontal),(\alpha + 1,\beta, Horizontal)\ and\ (\alpha + 1, \beta, Vertical)$$

#### Lines Around a Square

This function is relatively simple compared to the last funcion, given a square we have to find all the lines around that square.



```python
def aroundSquare(x,y):
    return [LineID(x,y,True),LineID(x,y,False),LineID(x+1,y,True),LineID(x,y+1,False)]
```

All squares have 4 lines surrounding it. Two horizontal lines and two vertical lines.

For the square with coordinate $$\alpha ,\beta$$, we can represend the lines around it as

$$ (\alpha, \beta, Horizontal), (\alpha, \beta, Vertical), (\alpha + 1, \beta, Horizontal)\ and\ (\alpha, \beta + 1, Vertical)$$

## Choose N

```python
def nTrue(vars,n):
    return list(map(lambda x:list(x),list(combinations([-i for i in vars],n+1))))+list(map(lambda x:list(x),list(combinations(vars,len(vars)+1-n))))
```

This is just one line of code but it took me a lot of time and creativity to come up with this. Initially my plan was to make multiple functions for each of the cases I would have to deal with but that would be too cringe. 


The Choose N function is a CNF representation that N and exactly N of the variables from the ones given need to be true. Making this function would have been easy if the constraint of CNF was not given. I sat down and wrote down various of these conditions and then manually converted them CNF form using Karnaugh-Maps[^KMAPS]. I thought this was to no avail, unsatisfied I decided to go sleep. Mid-sleep I came up with a better way to construct this function. While implementing this algorithm, I came up with an even better one. The original algorithm[^other], I recommend not checking out what the other algorithm if you don't understand boolean algebra.

For Exactly N variables to be true, we can say that at least N variables need to be true and at most N variables need to true.


$$n\leq x \leq n \Leftrightarrow x=n$$ or 
$$(AtMostN)\land (AtLeastN) \equiv (N\ True)$$

I used python's itertools library to help me out which is [beatuifully written and which I take inspiration from.](https://www.youtube.com/watch?v=jUM_Dpt6yu0)

I believe every novice python programmer needs to know about python's [itertools module](https://www.youtube.com/watch?v=p8FUoSIyIVY&t=282s). I will be using itertool's combinations function[^Combinations]. It gives us ways we can arrage p items in to r length lists or the ways we can choose r elements from list of p items. ([it gives the combinations not permutations](https://www.youtube.com/watch?v=0ZsSRx0o0zE))

#### At Least N
Let the number of variables here be len, and N the number of variables we want to be true. $$len-n$$ is the number of variables that are therefore false. So if we choose one more than $$len-n$$ variables, at least one has to be true no matter what. Therefore if we add all the ways of choosing any $$len-n+1$$ from the variables represented in the CNF form, the expression will be True if at least N variables are True.

If we have variables $$(\alpha ,\beta ,\gamma ,\delta)$$ and we want at least 1 true. We can represend it as

$$(\alpha \lor \beta \lor \gamma \lor \delta)$$

Similarly if we want at least two of those 4 variables to be true, we can write it as

$$ (\alpha \lor \beta \lor \gamma) \land (\alpha \lor \beta \lor \delta) \land (\alpha \lor \gamma \lor \delta) \land (\beta \lor \gamma \lor \delta)$$

Similarily if we want at least 3 of those 4 variables to be true, we can write it as

$$(\alpha \lor \beta)\land (\alpha \lor \gamma)\land (\alpha \lor \delta) \land (\beta \lor \gamma) \land (\beta \lor \delta) \land (\gamma \lor \delta)$$

For the SAT Solver we are using, we have to represnt the CNF form in terms of items in a 2 degree nested list or a list with lists inside of it. The items in the list inside the list are in disjunction\OR (At least one of the variables inside have to me true) whereas the lists inside the primarity list are in conjunction\AND (All the lists have to be true).

$$(\alpha \lor \beta)\land (\alpha \lor \gamma)\land (\alpha \lor \delta) \land (\beta \lor \gamma) \land (\beta \lor \delta) \land (\gamma \lor \delta)$$

would be represented as 

$$[[\alpha , \beta ],[\alpha , \gamma ],[\alpha , \delta ] , [\beta , \gamma ] , [\beta , \delta ] , [\gamma , \delta ]]$$

```python
combinations(vars,len(vars)+1-n)
```

Gives us all the ways to choose vars-n+1 variables from all the variables. Ufortunately, this is an object which contains tuples which needs to be converted to a list. For that reason we need to convert it to a lists of a lists as:

I learned about lamda operators when I friend Sarthak explained [$$\lambda$$ Calculus](https://en.wikipedia.org/wiki/Lambda_calculus) to me. You do not need to know about Lamda Calculus in order to understand the code, you can check out this resource[^lambda] that explains lamda maps in python.

```python
list(map(lambda x:list(x),list(combinations(vars,len(vars)+1-n))))
```

#### At Most N

In some sense, at most N is the same as a at least N. If have figured out how to implement, at least N we can easily implement at most N.

How? Well, if *at most* N variables are True then *at least* `len-N` must be false. Applying what we did before. Therefore if we choose one more than $$len-(len-n)=n$$ or $$n+1$$ variables, at least one of them must be false. To check that at leasy one of them false, we can apply negation (NOT) to the variables $$\neg \alpha$$ is True when $$\alpha$$ is False and False when $$\alpha$$ is true. We can find all the ways to choose n+1 variables and negate them so that the expression is True if at least $$len-N$$ variables are False or if at most N variables are True.

If we have variables $$(\alpha ,\beta ,\gamma ,\delta)$$ and we want at most 1 True (at least 3 False). We can represend it as

$$(\neg \alpha \lor \neg \beta)\land (\neg \alpha \lor \neg \gamma)\land (\neg \alpha \lor \neg \delta) \land (\neg \beta \lor \neg \gamma) \land (\neg \beta \lor \neg \delta) \land (\neg \gamma \lor \neg \delta)$$

From the 4 variables if we want at most 2 True (at least 2 False) we can represent it as

$$ (\neg \alpha \lor \neg \beta \lor \neg \gamma) \land (\neg \alpha \lor \neg \beta \lor \neg \delta) \land (\neg \alpha \lor \neg \gamma \lor \neg \delta) \land (\neg \beta \lor \neg \gamma \lor \neg \delta)$$

and so on.

This is similar to the code explained previously, the only difference is that I am negating all the variables by adding a negative sign in front of them. `[-i for i in vars]` creates a list where all the elements in vars become negative.

```python
list(map(lambda x:list(x),list(combinations([-i for i in vars],n+1))))
```
## Implementing Rules 2 and 3

```python
cnf=[]

for i in list(range(rows+1)):
    for j in list(range(cols+1)):
        cnf+=nTrue(aroundSquare(i,j),int(squares[i][j])) if (i<rows and j<cols and squares[i][j]!='.') else []
        for hori in [True,False]:
            for t in [True,False]:
                cnf+=[k+[-lineId(i,j,hori)] for k in nTrue(linesAround(i,j,hori,t),1)] if ((not hori or j<cols) and (hori or i<rows)) else []
```

`cnf` is the list to which will add all the clauses.

#### Implementing Rule 2

First we will enforce Rule 2: Numbers in a Cell. The number of lines around a square\cell is represented by the number inside the square\cell.

We can enforce this by iterating through all the cell and enforcing the condition that only N of those lines must be true. We sill use the `nTrue` and `aroundSquare` functions to help us in doing so. `int(squares[i][j])` gives us the number inside the square

```python
for i in list(range(rows)):
    for j in list(range(cols)):
        cnf+=nTrue(aroundSquare(i,j),int(squares[i][j]))
```

#### Implemeting Rule 3

Rule 3 states that the loop never crosses itself. This means that if we draw a line, we need to connect it exactly 2 lines, one on either point of the line. To understand how I have enforced Rule 3, you would have to understand 2 things in boolean algebra: *The Distributive Property* and *Implication*.

Implication is relatively easy to understand since we use the word **implies** regularly. A implies B can be represented as

$$A\implies B\equiv \neg A \lor B$$

This means that is A is true then B must be true. It is possible that B is true and A is false.

For example, let A be the statement that I'm Indian and B the statement that I'm South Asian. 

Here A implies B. If I'm Indian I must be South Asian, but I could be South Asian without being Indian (Lets say if I were Pakistani).

The second thing we need to understand is the Distributive Property. You probably already know about it because of arithmetic.

$$x \times (y+z) = xy + xz$$

This same law applies in Boolean Algebra as well

$$\alpha \lor (\beta \land \gamma) \equiv (\alpha \lor \beta) \land (\alpha \lor \gamma)$$

Using these two we can enforce Rule 3. If a line is present it implies that there are 2 lines attached to it. One line is attached to the anterior (pre) point of the line and the other to the posterior point of the line.

Let $$\alpha$$ be a line and $$(\zeta ,\theta ,\phi)$$ represend the lines connected to one of its points. At least of one $$(\zeta ,\theta ,\phi)$$ needs to be true represented in CNF, let this representation be $$\tau$$

$$\alpha \implies \tau$ \equiv \neg \alpha \lor \tau$$

$$\tau \equiv (\neg \zeta \lor \neg \theta) \land (\neg \zeta \lor \neg \phi) \land (\neg \theta \lor \neg \phi) \land (\zeta \lor \theta \lor \phi)$$

Therefore the entire condition can be represented as 

$$(\neg \alpha \lor \neg \zeta \lor \neg \theta) \land (\neg \alpha \lor \neg \zeta \lor \neg \phi) \land (\neg \alpha \lor \neg \theta \lor \neg \phi) \land (\neg \alpha \lor \zeta \lor \theta \lor \phi)$$

## Footnotes and Bibliography

[^Puzzle Ninja]: [Puzzle Ninja By Alex Bellos](https://www.amazon.com/Puzzle-Ninja-Against-Japanese-Masters/dp/145217105X/)
[^PROOF]: https://www.jstage.jst.go.jp/article/ipsjjip/20/3/20_709/_article/-char/en
[^paper1]: https://david-westreicher.github.io/static/papers/ba-thesis.pdf#page=34&zoom=100,158,576
[^paper2]: https://www.cs.ru.nl/bachelors-theses/2021/Gerhard_van_der_Knijff___1006946___Solving_and_generating_puzzles_with_a_connectivity_constraint.pdf
[^other]: I could have first created the condition in Disjunctive Normal Form (let's call it f), applied De Morgans Law to f and from a contradiction containing all variables in Conjunctive Normal Form, I would remove all the elements that were common between it and the modified f. This would have been more ineffecient? 
[^KMAPS]: https://www.geeksforgeeks.org/introduction-of-k-map-karnaugh-map/
[^Combinations]: https://docs.python.org/3/library/itertools.html#itertools.combinations
[^lambda]: https://cs.stanford.edu/people/nick/py/python-map-lambda.html