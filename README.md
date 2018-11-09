# Feup Mfes Summary
Some useful scripts

### Execute custom examples
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
Depois `execute`, na janela de execution ver a tab `executor` e escrever lá o query, por exemplo: `{A0 + D0} <: Rel.r`
