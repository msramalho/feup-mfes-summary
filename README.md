# Feup MFES Summary (Alloy)

## Execute custom examples
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

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

### NNN ________

```als

```

