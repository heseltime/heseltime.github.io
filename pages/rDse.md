---
layout: Post
permalink: /rDse
title: Software Engineering Studies Documentation and Research-Projects/Interests
feedformat: none
---

@University of Applied Sciences Upper Austria - Hagenberg Campus, Hagenberg: I am following a rigorous Software Engineering curriculum for a second Bachelor's degree in the subject, focussing mostly on the technical underpinnings and languages, but also related topics and soft skills, from project management through to modeling languages and approaches.

**What follows is documentation of my research project and thesis in Document Processing along with a list of courses matching my transcript from school below.** 

**Update 1**: In-progress presentation at [Wolfram Summer Program 2024](https://www.wolframcloud.com/obj/heseltine/Published/mentor-talk-wolfram-summer-program-2024.nb) ([Repo](https://github.com/heseltime/wsrp2024-mentor-talk)), with a special emphasis on using WL for Software Engineering and thinking of Mathematica notebooks as documents, informed by my ECM (Enterprise Content Management) background.

![Recursion Flow](..\assets\img\wsrp\Artboard2@2x.png)

The technical concept focus was recursing through WL expressions, as per this project's requirements. Also, here's me explaining it to a room full of Wolfram Summer Research Program high schoolers to get them thinking about project ideas involving document processing.

![WSRP Mentor Talk](..\assets\img\wsrp\mentor-talk-graphic.jpg)

# Thesis with RISC (Research Institute Symbolic Computation) also @Hagenberg: Mathematical Document Processing #

Not just Document Processing (often: Document Preparation), but <b>Mathematical</b> Document Processing: the goal a translation tool from Mathematica to LaTeX in the context of RISC's Theorema Tool. [Details directly from RISC](https://risc.jku.at/th/theorema-project-document-processing/) (RISC is an international institute with a research focus on various branches of symbolic computation).

**Update (0)**: [here an initial **presentation** given about the project (some DE, but the main content is in EN)](..\assets\pdf\Tma2TexPresentation1.pdf) scheduled for completion by June/July 2024. 

<!-- Final Presentation (January 2024): slides with thumbnail -->

<div class="risc" id="risc-work" style="background-color: #c7d7eb;">
    <h2>RISC Thesis 2024</h2>
    <h4><b>Update 2</b>: <a href="../assets/pdf/Tma2TeX-September-Draft.pdf">My submitted final draft is now available!</a> (September 2024)</h4> 
    <h5><b>Update 2 (a)</b>: <a href="../assets/pdf/Tma2TeX-December.pdf">Of course there is a final, final Draft!</a> (December-Version (2024) without official cover sheet.)</h5> 
    <p>But I don't get to complain, Theorema, the topic I worked on is more than 20 years old: (abstract) work takes time.</p>
    <h5><b>Update 2 (b)</b>: <a href="../assets/nbs/seminar-talk-Tma2TeX-2024.nb">(NB) Seminar Talk</a> (December 2024) and <a href="../assets/nbs/BuildingApplicationsWithTheWolframCloud.nb">(NB) Building Applications with the Wolfram Cloud (WolframU)</a></h5> 
    <a href="../assets/pdf/Tma2TeX-September-Draft.pdf"><img src="../assets/img/Tma2Tex-thumb.png" alt="My Final Draft Submission For Download" style="display: block; margin: 20px auto; max-height: 590px; height: 100%; background-color: #c7d7eb;"></a>
    <p>This thesis fulfills the requirements <a href="https://risc.jku.at/th/theorema-project-document-processing/">formulated by the Research Institute Symbolic Computation (RISC)</a>, mainly responding to <i>the task [of setting up] an environment for preparing entire (big) mathematical documents in <a href="https://arxiv.org/abs/1307.1945">Theorema 2.0</a></i>.</p>
    <h3>The meaning of this project to me, aside from getting me a job at Wolfram Research, is conceptual and related to Stephen Wolfram's notion of a <a href="https://writings.stephenwolfram.com/2019/05/what-weve-built-is-a-computational-language-and-thats-very-important/">computational</a> language, as well as the overall symbolic take on computing and programming.</h3> 
    <p>Since this tooling offers a wrapper for the ca. 2020-onward Large Language Models (LLMs), a way to not only contextualize, but concretely plug in language modeling-level results for reliably accurate outputs. But hanging out with the original idea for a moment, here's Stephen Wolfram's take on what makes Wolfram Language a computational language, beyond a programming language: <i>In most standard programming languages, x on its own without a value doesn’t mean anything; it has to stand for some structure in the memory of the computer. But in a computational language, one’s got to be able to have things that are purely symbolic, and that represent, for example, entities in the real world—that one can operate on just like any other kind of data.</i> In my thesis work, I <b>connect this line of thinking to First Order Predicate logic, the logic of <a href="https://risc.jku.at/sw/theorema/">Theorema</a>, but then circle back to Mathematica notebooks as documents, and so this work and especially its practical component (the work wraps an engineering degree after all), is a document processing project</b> in the end.</p>
    <h3>My <a href="/rDai">academic home in Linz</a> forms the LLM-side of the equation.</h3>

    <h2>From the Preface ... </h2>
    <p>I would like to thank, in chronological order as pertains to this thesis, the following persons who enabled this course of study and thesis in Hagenberg, both in the professional and the educational context:</p>

    <ul>
        <li><b>At the Red Cross Blood Bank and Transfusion Center in Upper Austria, at Linz General Hospital</b>: <b>DI Dr. Stephan Federsel</b> and <b>Dr. Norbert Niklas</b>, IT leadership at the blood bank, for making generous allowances for pursuit of the part-time, Friday- (and Saturday-)form of the Software Engineering curriculum in Hagenberg, and for teaching me the value of quality software documentation.
        </li>

        <li><b>My advisor Assoc. Univ.-Prof. DI Dr. Wolfgang Windsteiger</b>, but also the course management (Studiengangsleitung) for Software Engineering, for being blind to bureaucratic boundaries between Johannes Kepler University (JKU) and Fachhochschule Oberösterreich (Campus Hagenberg), so that the present thesis work could be situated at RISC, a JKU institute, but explore this Software Engineering topic in the domain of RISC’s general interest in Symbolic Computation and using Mathematica in particular, and Prof. Windsteiger for his patience as well.</li>

        <li><b>The wonderful people in Educational Outreach under Mads Bahrami, PhD, at Wolfram Research</b>, headquartered in Champaign, Illinois, for not just allowing me to participate in the Wolfram Summer School 2023, but also fully funding it, significantly accelerating learning of the Wolfram Language, and subsequently accepting my application for the role of Software Engineer in the Cloud Team at the company. In a full circle journey, I am teaching at Wolfram Summer Research Program 2024, the format for high schoolers, drawing on the understanding gained in the writing of this thesis, as well as the summer school, and looking forward to presenting results and methods deployed here to eager young students &mdash;</li>

        <li>&mdash; for which, again, I am thankful to Wolfram Research but especially <b>my manager</b>, <b>John Pacey</b>, for allowing this kind of flexibility. The same I would also like to thank for use of learning and time on the job as the work placement requirement in the field of Software Engineering for official completion of the course of study.</li>

        <li>Finally, I would also like to thank my colleague and <b>team lead</b>, <b>Joel Klein</b>, for the training in using Wolfram Language as an engineering tool and patience, and very often his marked pleasure, in answering my many technical questions.</li>
    </ul>

    <p>I am immensely grateful for your trust, patience (once again), and also your commitment to continued learning and quality of your work, which is truly inspiring.</p>
</div>



# Software Engineering Full Curriculum (Bachelor's of Science in Engineering '24) #
<div id="hagb-curriculum"></div>
## *sixth semester

_This semester also credits for practical, internship-type work, which I am completing with Wolfram Research, [as part of my consulting work with the company.](/wolfram) Will include a short write-up as well: I will link it when I have it, maybe with production code samples and analysis if I can get permissions, on the topic of using WL for Software Engineering._

- *Lecture + Exercise: Software Development with Enterprise Technologies: Java-Stack focus initially, covering Modules (JPMS) and Build Systems (Maven and Gradle), ORM (JPA and Hibernate), [Spring (Boot)](/portfolio#open-api), but also Entity Framework - see .NET last semester.
- Combined Lecture & Exercise: Current Trends in Web Technologies (Blockchain, NFTs, ... all the good stuff)
- Study Project in C# with Industry Partner in Hagenberg ([ventopay](https://www.linkedin.com/company/ventopay-gmbh)) - Part II
- Lecture + Exercise: Distributed and Parallel Systems - favorite exercise project: [Toilet simulation](https://github.com/heseltime/VPSToilet) for parallelizing (synchronizing) toilet goers (producers) with their local facilities (consumers).
- *Lecture: Information Management: a nice full circle back to where getting serious about software (in my particular AI/ML context) started - the _IT department_ (in my case, of a Red Cross blood bank at the height of the global onset of Covid-19). In the end all development has to fit into a cohesive IT (IM) structure, otherwise it is 100% pointless. Though, I will say, my way in was always _**processes**_, and not hardware outfitting and helpdesk management, essential as these are for overall IM, say, in the ITIL framework.

## *fifth semester

- *Lecture + Exercise: Component-Oriented Software Engineering (C# and .NET)

    - _to add a personal note, **this** was the most challenging course (for me) in the whole studies: getting really specific about OO programming as implemented by Microsoft and with all the .NET framework as it makes provisions for async programming, databases and web platforms, was the task. I motivated myself to study this stuff by connecting to my Work in WL, in fact literally: you can, it turns out, [call the WL kernel **fairly easily** from a .NET program](https://github.com/heseltime/SWK5-W-WolframNETLink), allowing for a radical extension of programming capabilities into the Mathematica domain - it's pretty cool._

- *Lecture + Exercise: Web-Architectures and Frameworks (Angular focus)
- Lecture + Exercise: Virtualization Tooling (Docker focus)
- Lecture + Exercise: ~~Mobile Computing~~ Advanced Python, [credited from work over at JKU](/rDai#housekeeping) - sometimes you have to focus, in my case [AI-oriented work](/rDai) at this time. I played around with Swift as part of [my Bachelor-level prep, in AI _and CS_](/rDai#housekeeping), for my AI-Masters at JKU, as far as mobile goes - this course would have been in Kotlin. It's the one course from the full curriculum I did not do.
- Lecture: IT Law (Austria/EU focus, but the concepts travel)
- Study Project in C# with Industry Partner in Hagenberg ([ventopay](https://www.linkedin.com/company/ventopay-gmbh)) - Part I
- Thesis (see above) + Thesis Seminar

## fourth semester

- Lecture + Exercise: Graph Theory/Intermediate Python
- Lecture + Exercise: Modern Platforms Programming (C++ and Java/C#)
- Lecture + Exercise: Database-Systems and Semi-Strutured Data
- Lecture + Exercise: Computer Graphics and Image Processing
- Lecture + Exercise: Thesis Research Prep Course
- Lecture + Exercise: Software Development Methodologies - Usability Engineering
- Lecture + Exercise: Software Development Methodologies - Testing and Test-Automization
- Lecture + Exercise: Business Process Management
- Lecture + Exercise: Scripting Languages/PHP-Web-Project

## third semester

- Lecture + Exercise: Math 2 - Statistics
- Lecture + Exercise: Classic Programming Languages (C and C++)
- Lecture + Exercise: Advanced Computer Networking
- Lecture + Exercise: Database-Systems
- Lecture + Exercise: Software Development Methodologies - Modern Tools and Processes
- Lecture + Exercise: Software Development Methodologies - UML-Modeling
- Lecture + Exercise: Web Development/Web-Project

## second semester

- Lecture + Exercise: Math 1 - Linear Algebra
- Lecture + Exercise: Advanced Algorithms and Datastructures (more PASCAL*)
- Lecture + Exercise: Object Oriented Programming (more PASCAL, all of first year was PASCAL*)
- Lecture + Exercise: Advanced Operating Systems
- Lecture + Exercise: Computer Networking
- Lecture + Exercise: Databases and Data Modeling
- Lecture + Exercise: Advanced Software Project Engineering
- Lecture + Exercise: Advanced Mircoeconomics/Accounting


## first semester

- Lecture + Exercise: Logic and Math 0
- Lecture + Exercise: Elementary Algorithms and Datastructures (PASCAL as language of instruction!*)
- Lecture + Exercise: Basic Concepts of Programming (more PASCAL*)
- Lecture + Exercise: Fundamentals of Computer Science and Computer Architecture
- Lecture + Exercise: Software Project Engineering
- Lecture + Exercise: Microeconomics
- Exercise/Regular Workshop: Holding Technical Presentations
- Exercise: Operating Systems and Linux Basics

*PASCAL as language of instruction: the idea is to teach a language most people have not touched yet and develop the concepts in that language. The language's inventor, Niklaus Wirth, actually designed the langauge for teaching purposes. I think the approach makes sense. From PASCAL I studied C, then C++, Java, C#, JavaScript and Scripting Languges like PHP and Swift, very methodologically.

[Translated from the German](https://www.fh-ooe.at/campus-hagenberg/studiengaenge/bachelor/software-engineering/alle-infos-zum-studium/studienplan-vollzeit/) and with my own notes.

## ++ another note

When it comes to development work, what I notice time and time again, is that there is so much IT/admin involved to get to a place where you can effectively "develop" (also the soft wrappers involved in getting the specs, if those are not a given), that I would really consider any and all work in that domain as much of an asset as any of the formal skills learned according to the list above. 

This is where Software Engineering is as much an art and a coordination (and so on) soft skill as an engineering discipline.

<nav class="nav">
    <ul class="nav__list">
        <a href="/" class="nav__link">
            <i class="ri-home-5-line"></i>
            <span class="nav__name">
                Home
            </span>
        </a>

        <a href="/notes" class="nav__link">
            <i class="ri-swap-line"></i>
            <span class="nav__name">
                Feed
            </span>
        </a>

        <a href="/portfolio" class="nav__link">
            <i class="ri-slideshow-2-line"></i>
            <span class="nav__name">
                Portfolio
            </span>
        </a>

        <a href="/rDai" class="nav__link">
            <i class="ri-robot-line"></i>
            <span class="nav__name">
                AI
            </span>
        </a>

        <a href="/rDse" class="nav__link active-link">
            <i class="ri-command-line"></i>
            <span class="nav__name">
                Software
            </span>
        </a>

        <svg class="indicator" width="94" height="56" xmlns="http://www.w3.org/2000/svg">
            <ellipse cx="47" cy="28" rx="24" ry="28"/>
            <path d="M24 20C24 20 28 55.9999 48 56L0 55.9997C18 55.9998 24 20 24 20Z"/>
            <path d="M70 20C70 20 66 55.9999 46 56L94 55.9997C76 55.9998 70 20 70 20Z"/>
        </svg>
    </ul>

    <script src="{{ site.baseurl }}/assets-liquid-nav/js/main.js"></script>
</nav>