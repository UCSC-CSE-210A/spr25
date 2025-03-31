---
title: "Schedule"
layout: splash
days:
  - 2025-03-31 00:00:00-07:00
  - 2025-04-02 00:00:00-07:00
  - 2025-04-04 00:00:00-07:00
  - 2025-04-07 00:00:00-07:00
  - 2025-04-09 00:00:00-07:00
  - 2025-04-11 00:00:00-07:00
  - 2025-04-14 00:00:00-07:00
  - 2025-04-16 00:00:00-07:00
  - 2025-04-18 00:00:00-07:00
  - 2025-04-21 00:00:00-07:00
  - 2025-04-23 00:00:00-07:00
  - 2025-04-25 00:00:00-07:00
  - 2025-04-28 00:00:00-07:00
  - 2025-04-30 00:00:00-07:00
  - 2025-05-02 00:00:00-07:00
  - 2025-05-05 00:00:00-07:00
  - 2025-05-07 00:00:00-07:00
  - 2025-05-09 00:00:00-07:00
  - 2025-05-12 00:00:00-07:00
  - 2025-05-14 00:00:00-07:00
  - 2025-05-16 00:00:00-07:00
  - 2025-05-19 00:00:00-07:00
  - 2025-05-21 00:00:00-07:00
  - 2025-05-23 00:00:00-07:00
  - 2025-05-28 00:00:00-07:00
  - 2025-05-30 00:00:00-07:00
  - 2025-06-02 00:00:00-07:00
  - 2025-06-04 00:00:00-07:00
  - 2025-06-06 00:00:00-07:00

holidays:
  - description: Memorial Day
    hide_time: true
    date: 2025-05-26 00:00:00-07:00
    type: raw_event
    name: Holiday
    color: "#e9ffdb"
---

<style type="text/css">
span.discussion { color: #dc267f; font-weight: bold }
span.lecture { color: #fe6100; font-weight: bold }
span.noclass { background-color:rgb(234, 174, 184); font-weight: bold }
tr:nth-child(odd)   { background-color:#eee; }
tr:nth-child(even)    { background-color:#fff; }
tbody>tr>:nth-child(3) {min-width:5em;}
</style>

## Schedule of topics (subject to change!)
{% assign lec = 0 %}

| Date             | Topic                                          | Notes
|------------------|------------------------------------------------|------------------------------------------------------------------------------------------------------------
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Course overview and basics of Coq    | [Course overview](course-overview.html); [Preface](); [Basics]()
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Induction and datastructures         | [Induction](); [Lists]()
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            |
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Polymorphism, functions as data      | [Poly]()                                              
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | <span class="noclass">No class; Prof. Arden out of town</span>  | video links coming soon
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | <span class="noclass">No class; Prof. Arden out of town</span>  | video links coming soon
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Logic in Coq                         | [Logic]()                                                        
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            |
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Inductively defined propositions     | [IndProd](); [ProofObjects]()                                    
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            |
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Total and partial maps; IMP          | [Maps](); [Imp](); [ImpParser](); [ImpCEvalFun]()
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | IMP: modeling an imperative language |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Program equivalence                  | [Equiv]()
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Hoare Logic                          | [Hoare](); [Hoare2]()
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
