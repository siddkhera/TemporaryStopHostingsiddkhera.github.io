---
title: Solving Slitherlink Using Boolean Satisifiability
date: 2022-10-03 00:00:00 +0530
categories: [SAT/SMT Solver, Slitherlink]
tags: [boolean satisfiability, propositional logic, SMT/SAT Solvers, slitherlink]
toc: true
math: true
---

## What is Slitherlink?

Slitherlink is a Japanese Puzzle Game I love. I'd made a video explaining it a year ago, you can check it out if you don't know about the game. (I apologise for my voice in advance, I was half asleep)

<iframe src="https://www.youtube.com/embed/EMuvNXjdWEE" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>



During the summer holidays, while solving Sitherlink puzzles on <https://www.puzzle-loop.com/>, I suddently had the urge to make a Slitherlink Solver. I'd seen many people make Soduku solvers, 

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
        if(i<rows and j<cols and squares[i][j]!='.'):
            cnf=cnf+nTrue(aroundSquare(i,j),int(squares[i][j]))
        if(j<cols):
            for k in nTrue(linesAround(i,j,True,True),1):
                cnf+=[k+[-LineID(i,j,True)]]
            for k in nTrue(linesAround(i,j,True,False),1):
                cnf+=[k+[-LineID(i,j,True)]]
        if(i<rows):
            for k in nTrue(linesAround(i,j,False,True),1):
                cnf+=[k+[-LineID(i,j,False)]]
            for k in nTrue(linesAround(i,j,False,False),1):
                cnf+=[k+[-LineID(i,j,False)]]

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

