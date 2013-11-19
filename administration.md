---
layout: frontpage
title: Administration
---

# Administrative Flotsam

## Weekly Meeting Notes

Notes from our weekly meetings:

{% for post in site.posts %}
* [{{ post.title }}]({{ site.baseurl }}{{ post.url }})  {{ post.date | date_to_string }}
{% endfor %}
