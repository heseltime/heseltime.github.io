# Based on Jekyll Garden v 0.4!
From the base project: "Jekyll Garden theme lets you publish your [Obsidian](https://obsidian.md/) vault (or a subset of it) as a Jekyll static website. The theme is markdown and Obsidian setup friendly. You can use your own server or Github page to set up your SSG."

## Documents and links from the base project
-  [Demo website](https://jekyll-garden.github.io/)
-  [Personal Website](https://hiran.in/)
-  [Feature List](https://jekyll-garden.github.io/post/features)
-  [How to Setup](https://jekyll-garden.github.io/post/how-to)

What follows are notes on my process improving the website in some small regards, that make for added look and feel, so end up being important on that side of things.

## Further Development (WDP3): Additions

### Cross-Page Nav Bar (CSS, JavaScript, SVG)

Goal: In terms of content, draw together different directions of my studies. Technically, attempt an implementation to add on to the Jekyll Garden (JG) framework base. In terms of design, I like this kind of fluid look [here](https://www.youtube.com/watch?v=argynmjupK8). The bar is placed on all pages too allow for easy switching between areas, the pages are static pages in the Jekyll garden project and kept current in Visual Studio Code (not Obsidian synching). The idea is to link to GitHub projects here containing university work and similar.

Method: Static pages implementation for research notes as opposed to Obsidian notes for rX Feed. The pages are made available via markup links, the navbar links to these. I set up five pages or so this way. Pages' content is edited in the project pages directory with markup files (.md).

The html content is tied in at the level of the pages in order to set the active page via CSS-class, and so that the bar appears below the content, but only for posts (from where its view behavior might still be manipulated). Assets are put into a parallel assets folder assets-liquid-nav (based on https://github.com/bedimcode/liquid-navigation-indicator) and linked to from _layout/Post.html

![Screenshot 2022-12-30 at 22 27 47](https://user-images.githubusercontent.com/66922223/210112885-580b9a31-b88f-460b-809b-ad8dcc32a9de.png)

I think this lower navbar is useful for naviagating across content in the website, as opposed to the top navbar, which focuses on portfolio, resume, etc. links, aimed at people checking out the website speedily. But I decided to not make the lower nav visible from home, instead only after navigating into Feed or Portfolio, so the website unfolds a bit.

![Screenshot 2022-12-30 at 22 27 57](https://user-images.githubusercontent.com/66922223/210112865-32ea64b2-51fe-4a6b-8517-5b7f3955f2a5.png)

The homepage has a very toned down version that allows the jump into this navigation:

![Screenshot 2022-12-30 at 23 15 12](https://user-images.githubusercontent.com/66922223/210115071-999d94d2-d121-4828-9995-22b658f477ca.png)

Technologies: CSS, Javascript, SVG (background). The javascript is implemented to move the background SVG, which only really comes out when linking to divs on one page, which I do not currently do, however.

### Favicons

Goal: Device-cross-functional favicons. Starting point:

![Screenshot 2022-12-30 at 21 45 31](https://user-images.githubusercontent.com/66922223/210110511-a32a81a0-c8e9-4513-9d1f-321a2236162d.png)


Method: Using WDP-source [Favicon generator](https://realfavicongenerator.net) and [How to Favicon in 2021](https://css-tricks.com/how-to-favicon-in-2021/), which is recent enough. I basically followed this tool, putting the icons in my asset folder rather than root.

I am also using a favicon version generated here to add some branding to the title in the top nav.

![Screenshot 2022-12-30 at 21 30 50](https://user-images.githubusercontent.com/66922223/210109781-602f42be-f84e-49db-9528-921b02821824.png)

**Update: I only noticed the following unsharp look of this icon later, and on a different screen.

![BFC17E0247684DF0857556A305635A1C](https://user-images.githubusercontent.com/66922223/210134587-8a79ca24-8063-4b23-a9ee-3484fb7db6e7.png)

**Fix: img-srcset tags, since the problem is high definition screen display. The improvement, on the same screen as before:

![30A2F2877F954CBDB2E00BE1F801E133](https://user-images.githubusercontent.com/66922223/210135219-20b75ff6-b8f4-4b44-9201-34e29639d711.png)

**([Source](https://www.mediaevent.de/html/srcset.html) for this approach.)

Very important, concerning favicons again: Emptying Chache between changes for testing (favicon info appears to be cashed a lot, certainly on Safari).

![Screenshot 2022-12-30 at 22 26 03](https://user-images.githubusercontent.com/66922223/210112809-3fe8584f-196f-486e-9f32-df30f699dc51.png)

I like the more strongly branded result.

## Further Development (WDP3): Improvements/Bug-Fixes

### Javascript Error in Day/Night Mode Switch Script

![Screenshot 2022-12-30 at 20 21 22](https://user-images.githubusercontent.com/66922223/210105352-88be52e6-ef86-477e-a119-3be955de5075.png)

This problem required a deep dive into the DevTools:

![Screenshot 2022-12-30 at 20 54 22](https://user-images.githubusercontent.com/66922223/210107450-2043cd50-352d-4b77-9c44-c3ccdba5e08d.png)

The secondary problem was encoding of the URL (I removed the prefix), but the issue remained, on exactly the first call (on load). It appears the ressource cannot be found the first time the script loads. So the solution was:

![Screenshot 2022-12-31 at 13 58 53](https://user-images.githubusercontent.com/66922223/210137662-f9c75d3e-fd2a-4457-876b-9741338ac07c.png)

I.e. waiting to make the changes. The module (modeswitcher.js) switches CSS themes on a button click and stores the dark/light preference in browser storage. There are now no errors on load.

### Metadata Update/Fix

Embarassing: the base project info was still in here. I updated it, including Open Graph data.

![Screenshot 2022-12-30 at 22 50 33](https://user-images.githubusercontent.com/66922223/210113953-b803e6cd-af8e-4b3e-991d-80e6b25f0453.png)
