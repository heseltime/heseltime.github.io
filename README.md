# Based on Jekyll Garden v 0.4!
From the base project: "Jekyll Garden theme lets you publish your [Obsidian](https://obsidian.md/) vault (or a subset of it) as a Jekyll static website. The theme is markdown and Obsidian setup friendly. You can use your own server or Github page to set up your SSG."

## Documents and links from the base project
-  [Demo website](https://jekyll-garden.github.io/)
-  [Personal Website](https://hiran.in/)
-  [Feature List](https://jekyll-garden.github.io/post/features)
-  [How to Setup](https://jekyll-garden.github.io/post/how-to)

## Further Development (WDP3): Additions

### Cross-Page Nav Bar (CSS, JavaScript, SVG)

Goal: In terms of content, draw together different directions of my studies. Technically, attempt an implementation to add on to the Jekyll Garden (JG) framework base. In terms of design, I like this kind of fluid look [here](https://www.youtube.com/watch?v=argynmjupK8). The bar is placed on all pages too allow for easy switching between areas, the pages are static pages in the Jekyll garden project and kept current in Visual Studio Code (not Obsidian synching). The idea is to link to GitHub projects here containing university work and similar.

Method: Static pages implementation for research notes as opposed to Obsidian notes for rX Feed. The pages are made available via markup links, the navbar links to these. I set up five pages or so this way. Pages' content is edited in the project pages directory with markup files (.md).

The html content is tied in at the level of the pages in order to set the active page via CSS-class, and so that the bar appears below the content, but only for posts (from where its view behavior might still be manipulated). Assets are put into a parallel assets folder assets-liquid-nav (based on https://github.com/bedimcode/liquid-navigation-indicator) and linked to from _layout/Post.html

I think this lower navbar is useful for naviagating across content in the website, as opposed to the top navbar, which focuses on portfolio, resume, etc. links, aimed at people checking out the website speedily. But I decided to not make the lower nav visible from home, instead only after navigating into Feed or Portfolio, so the website unfolds a bit.

Technologies: CSS, Javascript, SVG (background). The javascript is implemented to move the background SVG, which only really comes out when linking to divs on one page, which I do not currently do, however.

### Favicons

Goal: Cross-functional favicons.

Method: Using WDP-source [Favicon generator](https://realfavicongenerator.net) and [How to Favicon in 2021](https://css-tricks.com/how-to-favicon-in-2021/), which is recent enough.


## Further Development (WDP3): Improvements/Bug-Fixes

### Javascript Error in Day/Night Mode Switch Script

![Screenshot 2022-12-30 at 20 21 22](https://user-images.githubusercontent.com/66922223/210105352-88be52e6-ef86-477e-a119-3be955de5075.png)

Dieses Problem brauchte einen Deep Dive in die DevTools, mit Nachexperimenten:

![Screenshot 2022-12-30 at 20 54 22](https://user-images.githubusercontent.com/66922223/210107450-2043cd50-352d-4b77-9c44-c3ccdba5e08d.png)

Man sieht, die URL zu den Icons wird falsch encodiert/aufgerufen.
