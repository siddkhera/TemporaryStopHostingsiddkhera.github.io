---
title: Satisfiability Course Meme
date: 2022-09-28 00:00:00 +0530
categories: [Youtube, Puzzles]
tags: [slitherlink, puzzles, youtube]

---

I loved the Automated Reasoning: Satisfiability course by Professor Hans Zantema from TU Eindhoven on Coursera. While he was explaining boolean multipliction using SAT solvers I burst out laughing as he pronounced **'fac'** short for factorise as **'f\*\*k'**.

<iframe width="560" height="315" src="https://www.youtube.com/embed/i4jNA3BzVA0" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

Jokes apart, I loved this course and would 100% recommend others to take it. Somewhat dissapointed I didn't complete this course before starting the Slitherlink project so I wouldn't have spent hours trying to come up with this algorithm.

```python
def nTrue(vars,n):
    return list(map(lambda x:list(x),list(combinations([-i for i in vars],n+1))))+list(map(lambda x:list(x),list(combinations(vars,len(vars)+1-n))))
```

 If only I had moved on to the third week and learnt about converting formulas to CNF before. 😭
