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

Before I start explaining my project, here is the code. It's also on my [GitHub](github.com/siddkhera) !

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

