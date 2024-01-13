rem c:\bin\cat -v read-line.txt | c:\bin\sed "s/^/""/" | c:\bin\sed "s/$/""/"
rem c:\bin\cat -v read-line.txt | c:\bin\sed "s/"""/\\\\"""/g"
c:\bin\cat -v read-line.txt | c:\bin\sed "s/"""/\\\\"""/g"| c:\bin\sed "s/^/printf(""/" | c:\bin\sed "s/$/\\\n/" | c:\bin\sed "s/$/"");/" > read-line-coded.txt
