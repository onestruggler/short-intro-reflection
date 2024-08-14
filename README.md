This is a short introduction to Agda's reflection mechanism. It consists of three files named "ShortIntroReflection" with almost the same content for different use.

1) The .pdf file is the ready content. It is compiled from the .lagda.tex file by the standard way of compiling a lagda file:

agda --latex ShortIntroReflection.lagda.tex
cd latex
xelatex ShortIntroReflection.tex

(you need copy "agda.sty" file to this folder)

2) The .lagda.tex is the tex or lagda source file.

3) The .agda file is the original version. The code is the same as .lagda.tex and but the comment is far less polished. Just in case for someone to quickly run the code.

This introduction is still in a draft phase to some extent. For example, it only covers a smal fragment of Agda's reflection mechanism.
