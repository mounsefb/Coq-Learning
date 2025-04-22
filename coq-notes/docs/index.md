# Welcome to a non comprehensive explanation of what I've learned from Coq SF classes 

The Sofware Foundations series is a collection of classes that anyone with an intermediate to advanced mathematical background can follow to understand the basics of functional programming and Coq coding.

## Review

I went through the Logical Foundations and Programming Language Foundations (sources : [softwarefoundations.cis.upenn.edu](https://softwarefoundations.cis.upenn.edu/)). The pedagogical value of these courses is undeniable but after completing the first modueles, I found myself struggling with memory lapses. That's why I'm writing this documentation to summarize what I've learned and make a comprehensive overview of these topics.

In my opinion, the major issue of SF is the lack of conciseness and recapitulation coupling with the absence of a tool to look in previously proved theorem and find something corresponding to your idea. You're easily finding yourself looking for the name of a theorem demonstrated a few modules before or proving again and again a proof already demonstrated a week ago but you forgot about it. That's why this documentation is here : to help me save time and energy...

## Recap

This documentation contains a recap of Basics, Induction, Lists, Poly, Tactics, Logic, IndProp, Maps, Imp from Language Foundations and Program equivalence, Small-step from Programming Language Foundations.

It follows a specific structure that I find understandable, one can have a different opinion on it :
    - a short description of the chapter 
    - a list of proven theorems 
    - a list of newly learned tactics

Will follow a global list of all defined functions, tactics and theorems.

This documentation isn't self-sufficent and not comprehensive regarding SF modules. 

For full documentation visit [mkdocs.org](https://www.mkdocs.org).

## Commands

* `mkdocs new [dir-name]` - Create a new project.
* `mkdocs serve` - Start the live-reloading docs server.
* `mkdocs build` - Build the documentation site.
* `mkdocs -h` - Print help message and exit.

## Project layout

    mkdocs.yml    # The configuration file.
    docs/
        index.md  # The documentation homepage.
        ...       # Other markdown pages, images and other files.
