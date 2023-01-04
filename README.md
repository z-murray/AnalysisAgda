# AnalysisAgda

# Update
Hello! This was a working repository for much of the work I did on implementing constructive analysis in the Agda proof assistant. It's a bit messy, so I decided to move everything into a new repository when I submitted my project, then undergraduate thesis, to the arXiv. The new repository, corresponding to the version submitted for the thesis, can be found at https://github.com/z-murray/honours-project-constructive-analysis-in-agda, which includes a link to the thesis. This version exists just to track my process at the time of development.

# Old Blurb
For my undergraduate summer project (under the supervision of Dr. Peter Selinger at Dalhousie University), I am implementing as much of Errett Bishop's constructive analysis in Agda as possible. This is a solo project. Others are not allowed to edit this repository, even if it becomes public. For the time being, it's listed here solely for version control and for anyone interested in seeing it.

Possible Questions and Answers:

(Q) What are your text references?
(A) See Errett Bishop's _Foundations of Constructive Analysis,_ or _Constructive Analysis_ by Errett Bishop and Douglas Bridges.

(Q) What Agda version and what library are you using?
(A) I'm using Agda 2.6.1.3 and the version of the Agda standard library available as of 13.05.2021.

(Q) Why constructive analysis instead of classical analysis?
(A) Two reasons. One, Agda is a proof assistant based on a constructive type theory, so the law of the excluded middle is not valid. I could probably add excluded middle as a posutlate, but that brings me to the second reason: I haven't learned constructive analysis yet, so I thought it'd be fun to learn.
