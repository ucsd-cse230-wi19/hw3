## CSE 230 HW 

## Download

1. Use the _fork link_ from the class website to create your private clone of the starter code.

2. Do `git clone https://github.com/ucsd-cse230-wi19/hw3-XXX` where `XXX` is your private repo.

## Link to Upstream

3. Link your clone to the "upstream" to get any updates

```
$ make upstream
```

after this you can get "updates" (in case we modify the starter code), with

```
$ make update
```

## Do the Assignment 

4. Edit the files and run LH 

```
$ make 
```

repeat this until LH says "SAFE"

## Submit 

5. Save (and submit) your work with:

```
$ git commit -a -m MESSAGE
$ git push
```


## Hint on Q2 

To implement `full_asimp` note that `NAExp` expressions look like:

	Plus (Var x1) (Plus (Var x2) ... (Plus (Var xn) (N c)))

and the key is to write a function 

	plus_naexp :: NAExp -> NAExp -> NAExp 

which, when given two `NAExp`s of the form
 
	a1 = Plus (Var x1) (Plus (Var x2) ... (Plus (Var xn) (N c)))

	a2 = Plus (Var y1) (Plus (Var y2) ... (Plus (Var ym) (N d)))

should essentially recursively go down the first expression till it hits the 
rightmost constant `N c` and replace it with `a2`-where-`d`-is-replaced with `c+d`.

To do the last step, you should write a function

	cplus :: Int -> NAExp -> NAExp 

such that `cplus n a` recurses on `a` until it finds its rightmost constant `c`
which is then replaced with `n+c`.

You should then use `cplus` to implement `plus_naexp a1 a2` by recursively 
going inside `a1` till you find its rightmost constant `c` which should then
be replaced by `cplus c a2`.


