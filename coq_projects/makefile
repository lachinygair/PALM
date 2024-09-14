PROJS_V10 = jordan-curve-theorem UnifySL tree-automata coquelicot
PROJS_V11 = StructTact InfSeqExt cheerios verdi buchberger fermat4 hoare-tut PolTac goedel weak-up-to dblib disel zchinese zfc dep-map chinese huffman angles coq-procrastination demos coqoban verdi-raft zorns-lemma fundamental-arithmetics
PROJS_V12 = coq-library-undecidability coqrel

.PHONY: all install v11 v10 v12

v10: | $(PROJS_V10)
v11: | $(PROJS_V11)
v12: | $(PROJS_V12)

buchberger:
	git clone https://github.com/coq-community/buchberger.git && cd buchberger && git checkout 0afb6f72a8a79bd6f40a2488fb2ea422d1bc5920 && make -j 24

fermat4:
	git clone https://github.com/coq-contribs/fermat4.git && cd fermat4 && git checkout f91289c096a9a9e74bbf018444f23010465246d3 && make -j 24

hoare-tut:
	git clone https://github.com/coq-community/hoare-tut.git && cd hoare-tut && git checkout 175f7b84911331057e942f03dd291cab7ee2d9e8 && make -j 24

PolTac:
	git clone https://github.com/thery/PolTac.git && cd PolTac && git checkout ebf4039cdf11c9d2f418e7e931463d8b77924a63 && make -j 24

goedel:
	git clone https://github.com/coq-community/goedel.git && cd goedel && git checkout 8c3e6e033be4dd0b1fce833d8fbf8b395ae31989 && make -j 24

weak-up-to:
	git clone https://github.com/coq-contribs/weak-up-to.git && cd weak-up-to && git checkout 6780e1d43bc9583d5e6fe47418980d4dbc8f6527 && make -j 24

dblib:
	git clone https://github.com/coq-community/dblib.git && cd dblib && git checkout 25469872c0ba99b046f7e5b8608205eeea5ac077 && make -j 24

disel:
	git clone https://github.com/DistributedComponents/disel.git && cd disel && git checkout c42a22f6dc7c3454eff21cc4f7423bd638b09a8c && make -j 24

zchinese:
	git clone https://github.com/coq-contribs/zchinese.git && cd zchinese && git checkout 906bb36960c230df143356ca4565771fe3008ef7 && make -j 24

zfc:
	git clone https://github.com/coq-contribs/zfc.git && cd zfc && git checkout ede7126560844c381c2b021003a8dbcb0668ecad && make -j 24

dep-map:
	git clone https://github.com/coq-contribs/dep-map.git && cd dep-map && git checkout c8a3df946a9e357284799b0ee40def47538bdc37 && make -j 24

chinese:
	git clone https://github.com/coq-contribs/chinese.git && cd chinese && git checkout 8af6c42f817721f7ac0f8f6fa6e123a455f4713e && make -j 24

huffman:
	git clone https://github.com/coq-community/huffman.git && cd huffman && git checkout 806e1035fe6554dc61958c0b5cb291203dd78194 && make -j 24

angles:
	git clone https://github.com/coq-contribs/angles.git && cd angles && git checkout a2ad15d45875765563fe756b06d29c3ae3ea4ab7 && make -j 24

coq-procrastination:
	git clone https://github.com/Armael/coq-procrastination.git && cd coq-procrastination && git checkout 199dab4435148e4bdfdf934836c644c2c4e44073 && make -j 24

demos:
	git clone https://github.com/coq-contribs/demos.git && cd demos && git checkout 399f6930fa7a9909b840d4a017159d0e06616940 && make -j 24

coqoban:
	git clone https://github.com/coq-community/coqoban.git && cd coqoban && git checkout f88486ca77cb0dc5aa0630b0e19b6cfa830593dc && make -j 24

verdi-raft:
	git clone https://github.com/uwplse/verdi-raft.git && cd verdi-raft && git checkout bdd358e4497c327624e3f8a2814fdfb11dca2934 && ./configure && make -j 24

zorns-lemma:
	git clone https://github.com/coq-community/zorns-lemma.git && cd zorns-lemma && git checkout aaf46b0c5f7857ce9211cbaaf36f184ca810e0e8 && make -j 24

fundamental-arithmetics:
	git clone https://github.com/coq-contribs/fundamental-arithmetics.git && cd fundamental-arithmetics && git checkout 8976d4ba6a5c53b7eb25d08921e592d200189431 && make -j 24

jordan-curve-theorem:
	git clone https://github.com/coq-contribs/jordan-curve-theorem.git && cd jordan-curve-theorem && git checkout 0072f59bea6ecc020c2042d1831c9cb9fc07fb85 && make -j 24

UnifySL:
	git clone https://github.com/QinxiangCao/UnifySL.git && cd UnifySL && git checkout cf4eec5d0d9f76b864d92a9e6df5bc3e8bb43d9d && make -j 24

tree-automata:
	git clone https://github.com/coq-contribs/tree-automata.git && cd tree-automata && git checkout 1d756a966aaee796ed46362d45ec9b0ddc6951ca && make -j 24

coquelicot:
	git clone https://github.com/thery/coquelicot.git && cd coquelicot && git checkout 52e16ffc38fe6605347ba32baf9b59ceeab6108d && git apply ../coquelicot.patch && ./configure && ./remake

coq-library-undecidability:
	git clone https://github.com/uds-psl/coq-library-undecidability.git && cd coq-library-undecidability && git checkout 6760922a777cb8080e19273399fe5798d4715111 && opam install -y . --deps-only && make -j 24

coqrel:
	git clone https://github.com/CertiKOS/coqrel.git && cd coqrel && git checkout 8e0c6a412ad9590d1de517b001751e01327c738a && ./configure && make -j 24

StructTact:
	git clone https://github.com/uwplse/StructTact.git && cd StructTact && git checkout 2e5fc017d51edfe2d15950e73b5b028ecb5d330b && ./configure && make -j 24 && make install

InfSeqExt:
	git clone https://github.com/DistributedComponents/InfSeqExt.git && cd InfSeqExt && git checkout 203d4c20211d6b17741f1fdca46dbc091f5e961a && ./configure && make -j 24 && make install

cheerios:
	git clone https://github.com/uwplse/cheerios.git && cd cheerios && git checkout 9c7f66e57b91f706d70afa8ed99d64ed98ab367d && ./configure && make -j 24 && make install

verdi:
	git clone https://github.com/uwplse/verdi.git && cd verdi && git checkout fdb4ede19d2150c254f0ebcfbed4fb9547a734b0 && ./configure && make -j 24 && make install
