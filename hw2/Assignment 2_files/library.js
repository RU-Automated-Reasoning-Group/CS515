
function gramarify(text){
	rules = text.split(';;');
	out = "";
	for(var x in rules){
		out += "<tr><td>" + rules[x] + "</tr></td>";	
	}
	return '<table style="table"><tbody>'+out+'</tbody></table>';
}

function quotify(text){
	return '<i>' + text + '</i>';	
}

function replacements(text){
	return text.replace(/-&gt;/g, "\\rightarrow");	
}

function rulify(text){
	topbot = text.split('---');
	toprule = replacements(topbot[0]);
	botrule = replacements(topbot[1]);
	out = "$\\frac{"+toprule+"}{"+botrule+"}$"; 
	out =  "<tr><td>" + out + "</tr></td>"
	console.log(out);
	return '<table style="table"><tbody>'+out+'</tbody></table>';
}

function doExample(name){
var text = document.getElementById(name).value;
eval(text);
}

function processTag(name, f){
	var x = document.getElementsByTagName(name);
	while(x.length>0){
		x[0].outerHTML = f(x[0].innerHTML, x[0].id);
	}
}

function jsexamplify(text, name){
	var out = '<p><textarea id ="Example1" cols="80" rows="15">' +
	text +
    '</textarea>' +
    '<input type="button"  onClick="doExample(\\"'+name+'\\");" value="Run '+name+'"></p>'
	return out;
}


function cite(bibentry){
	
	function cleanupNames(allnames){
		function cleanupName(names){
			if(typeof(names) == 'undefined'){ return ""; }
			
				
			names = names.replace(/\{-\}/g, '-');
			names = names.replace(/\\\'\{e\}/g, '&eacute;');
			
			names = names.replace(/\\v\{C\}/g, '&Ccaron;');
			
			names = names.replace(/\\\'y/g, '&yacute;');
			
			names = names.replace(/\\\'\{\\i\}/g, '&iacute;');
			names = names.replace(/\{/g, "");
			names = names.replace(/\}/g, "");
			names =  names.replace(/^\"/, "");
			var pos = names.search(',');
			if(pos > 0){
				var tt = names.split(',');
				names = tt[1] + ' ' + tt[0];
			}
			return names;
		}
		allnames = allnames.replace(/\n/g, ' ');
		var nlist = allnames.split(' and');
		var rv = "";
		for(i in nlist){
			rv += cleanupName(nlist[i]);	
			if(i < nlist.length-1){
				rv += ", ";
			}
		}
		return rv;
	}
	
	
	function cleanupTitle(names){	
		if(typeof(names) == 'undefined'){ return ""; }
		names = names.replace(/\{-\}/g, '-');
		names = names.replace(/\\\'\{e\}/g, '&eacute;');
		names = names.replace(/\\\'\{\\i\}/g, '&iacute;');
		names = names.replace(/\\_/g, "_");
		names = names.replace(/\{/g, "");
		names = names.replace(/\}/g, "");
		return names.replace(/^\"/, "");
	}
	function cleanupConf(code){
		if(typeof(code) == 'undefined'){ return ""; }
		code = code.split('/');
		return code[1].toUpperCase() ;
		
	};
	function noBrackets(text){
		if(typeof(text) == 'undefined'){ return ""; }		
		return text.replace(/\{/g, "").replace(/\}/g, "").replace(/^\"/, "");
	}
	
	var rv = cleanupNames(bibentry.author) + ",";
	if('url' in bibentry){
		rv += "<a href='"+  noBrackets(bibentry.url) + "'> <i>" + cleanupTitle(bibentry.title) + "</i></a>, ";
	}else{
		rv += " <i>" + cleanupTitle(bibentry.title) + "</i>, ";
	}
	
	
	
	rv += noBrackets(bibentry.year);
	
	return rv;
}

function citefy(name){
	var id = 0;
	if(name in footnotes){
		id =  footnotes[name].id;		
	}else{
		id = nextFootnote;
		nextFootnote += 1;
		footnotes[name] = {id:id,  val:cite(allPapers[name]), original:allPapers[name] }
		footnoteindex[id] = name;
	}	
	return '<sup><a href="#ref_'+id+'">' + id + '</a></sup>';
}

var nextFootnote = 1;
var footnotes = {};
var allPapers = {};
var footnoteindex = [];

function process(text){
	allPapers = {};
	var entries = text.split('@');
	
	proceedings = {};
	
	for(x in entries){
		var entry = entries[x];
		var obj = processEntry(entry);
		allPapers[obj.Key] = obj;		
	}
}

function processEntry(text){
	var pos = text.search("{");
	var firstComma = text.search(",");
	var name = text.substring(pos+1, firstComma);

	var rest = text;
	var rv = "";
	
	
	function readBracket(input){
		function rbHelper(text){
			var bopen = text.search("{");
			var bclose = text.search("}");
			if(bopen == -1 || (bclose != -1 && bclose < bopen) ){
				return bclose;	
			}else{
				var t = rbHelper(text.substring(bopen+1));
				return rbHelper(text.substring(bopen+t+2))+ bopen+t+2;
			}
		}
		var pos = input.search("{");
		var qpos = input.search('"');
		if(qpos >= 0 && (qpos < pos || pos < 0)){
			var tot = qpos;
			var text = input.substring(qpos+1);
			var pp = text.search('"');
			while( pp > 0 && text[pp-1]=='\\' ){
				tot += pp;
				text = text.substring(pp+1);
				pp = text.search('"');
			}
			return tot + pp+1;
		}
		return rbHelper(input.substring(pos+1))+pos+2;
	}
	
	
	var fields = {};
	function parseMore(){
		while(true){
		rest = rest.substring(rest.search(",")+1).trim();
		var nextEq = rest.search("=");
		if(nextEq == -1){ return false};
		var attrName = 	rest.substring(0, nextEq).trim();		
		rest = rest.substring(nextEq+1);
		var p = readBracket(rest);
		var attrVal = rest.substring(0, p);
		fields[attrName] = attrVal;
		rest = rest.substring(p);
		}
		return false;
	}
	
	parseMore();
	fields["Key"] = name;	
	fields["ALL"] = text;
	return fields;	
}



function loadAllFootnotes(file, rest){
	var request = new XMLHttpRequest();
    request.open('GET', file, true);
    request.send(null);
    request.onreadystatechange = function () {
        if (request.readyState === 4 && request.status === 200) {
            var type = request.getResponseHeader('Content-Type');
            if (type.indexOf("text") !== 1) {
            	process(request.responseText);
            	rest();
            }
        }
    }
}


function setNavBar(content, preamble){
	var entries = content.split(';');
	rv = "";
	if(preamble){
		rv += preamble;
	}
	for(var ent in entries){
		var io = entries[ent].split(',');
		if(io.length < 3){
			io = entries[ent].split(':');
			rv += "<div style = 'color: rgb(105, 12, 12);padding: 0px 8px 0px 10px;'>" + io[0] + "</div>";
		}else{
			var text = io[0];
			if(window.screen.width < 700){
				text = text.replace('Lecture', 'Lec');
				text = text.replace('Table of Contents', 'TOC');
			}
			if(io[1].length > 3){
				rv += '<a href="'+ io[1] +'">' + text + "</a>";
			}else{
				rv += '<div class="sidelink" style="color: rgb(42, 42, 42);">' + text + "</div>";
			}
				
		}
		
	}	
	document.getElementById('navigator').innerHTML = rv;
}

function loadNavBar(preamble){
	var request = new XMLHttpRequest();
    request.open('GET', 'lectures.txt', true);
    request.send(null);
    request.onreadystatechange = function () {
        if (request.readyState === 4 && request.status === 200) {
            var kind = request.getResponseHeader('Content-Type');
            if (kind.indexOf("text") !== 1) {
            	setNavBar(request.responseText, preamble);            	
            }
        }
    }
	
}



function splitcsv(str){
	var lst = [];
	while(str.length > 0 && lst.length < 5){
		var p1 = str.indexOf('"');
		var p2 = str.indexOf(',');
		if(p2 == -1){
			lst.push(str);
			return lst;
		}
		if(p2 < p1 || p1==-1){
			lst.push(str.substring(0, p2));
			str = str.substring(p2+1);
		}else{
			var p3 = str.indexOf('"', p1+1);
			var p4 = str.indexOf(',', p3);
			lst.push(str.substring(0, p4));
			str = str.substring(p4+1).trim();
		}
	}
	return lst;
}


function addSchedule(){
	const toc = document.getElementById('toc');
	if(!toc){
		return;
	}
	function Schedule(content){
		var entries = content.split('\n');
		rv = "<table>";
		rv += "<tr>";
		rv += "<th>Date</th>";
		rv += "<th>Title</th>";
		rv += "<th>Pset</th>";
		rv += "<th>&nbsp</th>";
    	rv += "</tr>"
		for(var ent in entries){
			var io = splitcsv(entries[ent]);
			if(io.length < 3){continue;}
			
			rv += "<tr>";						
			
			rv += "<td>" + io[0] + "</td>";
			if(io[2].length > 2){
				rv += "<td>" + io[1] + ": " + io[2] + "</td>";	
			}else{
				rv += "<td>" + io[1] + "</td>";
			}
			
			rv += "<td>" + (io[3]?io[3]:"&nbsp;") + "</td>";
			rv += "<td>" + (io[4]?io[4]:"&nbsp;") + "</td>";
			
			
			
			rv += "</tr>";
		}	
		rv += "</table>";
		toc.innerHTML = rv;
		
	}
	
	
	var request = new XMLHttpRequest();
    request.open('GET', 'Schedule.csv', true);
    request.send(null);
    request.onreadystatechange = function () {
        if (request.readyState === 4 && request.status === 200) {
            var type = request.getResponseHeader('Content-Type');
            if (type.indexOf("text") !== 1) {
            	Schedule(request.responseText);            	
            }
        }
    }
}

function addTOC(){
	function TOC(content){
		var entries = content.split(';');
		rv = "<ul>"
		for(var ent in entries){
			var io = entries[ent].split(',');
			if(io.length < 3){
				if(entries[ent].length < 5){
					
				}else{
					rv += '</ul>'+ entries[ent]  +"  <ul>";
				}				
			}else{
				if(io[1].length > 3){
					rv += '<li><a href="'+ io[1] +'">' + io[0] + ".</a> "+ io[2]  +"  </li>";
				}else{
					rv += '<li>' + io[0] + ". "+ io[2]  +"  </li>";
				}
					
			}
		}	
		rv += "</ul>"
		document.getElementById('toc').innerHTML = rv;
		
	}
	
	
	var request = new XMLHttpRequest();
    request.open('GET', 'lectures.txt', true);
    request.send(null);
    request.onreadystatechange = function () {
        if (request.readyState === 4 && request.status === 200) {
            var type = request.getResponseHeader('Content-Type');
            if (type.indexOf("text") !== 1) {
            	TOC(request.responseText);            	
            }
        }
    }
}


function popup(body){
	const node = document.getElementsByTagName("BODY")[0];
	const win = document.createElement("div");
	win.setAttribute("class", "popup");
	const img = document.createElement('img');
	img.src = 'icons/close.png';
	img.id = 'closer';
	img.width = 30;
	img.style.right = '0px';
	img.style.top = '0px';
	img.style.position = 'absolute';
	img.onclick = ()=>{
		node.removeChild(win);		
	};
	win.appendChild(img);
	const inner = document.createElement("div");
	inner.setAttribute('class', 'codeblock');
	inner.style.marginLeft = '0px';
	inner.style.marginRight = '0px';
	inner.style.marginBottom = '0px';
	inner.innerHTML = body;
	win.appendChild(inner);
	node.appendChild(win);
}


function renderBibtex(entry){
	var rv = '';
	for(var x in entry){
		rv += '    ' + x + ':' + entry[x] + ';\n';
	}
	return '@' + entry.ALL;
}

function showbib(name){
	popup(
			renderBibtex(footnotes[name].original)	
	);
}


function footrender(text, id){
	var rv = "";
	for(var i = 1; i < nextFootnote; ++i){
		var entry = footnotes[footnoteindex[i]].val;
		rv += '<p id="ref_'+i+'">' + i + ":" + entry + 
		'<a href="javascript:showbib(\''+footnoteindex[i]+'\')" style="font-size:80%;" >(bibtex)</a></p>'
	}
	return rv;
}

var slideid = 0;
var slideStore = {};

function nextSlide(id){
	var frame = document.getElementById('slideframe_' + id);
	var old = document.getElementById('slide_' + id);
	var store = slideStore[id];
	if(store.cur < store.all.length-1){
		store.cur = store.cur + 1;
	}else{
		store.cur = 0;
	}
	frame.replaceChild(store.imgs[store.cur], old);	
	var bar = document.getElementById('bar_' + id);
	bar.style.width = (((store.cur)*96.0 / (store.all.length-1))+ 1.0) + '%';
}



function growframe(id){
	var frame = document.getElementById('slideframe_' + id);
	frame.className = "alwaysbig";
	//frame.style.float = "none";
	//frame.style.width = "100%";
	var expand = document.getElementById('expand_' + id);
	expand.src = 'icons/shrink.png';
	expand.onclick = function(){ shrinkframe(id ); };
}

function shrinkframe(id){
	var frame = document.getElementById('slideframe_' + id);
	frame.className = "slideview";		
	var expand = document.getElementById('expand_' + id);
	expand.src = 'icons/grow.png';
	expand.onclick = function(){ growframe(id ); };
	
}

function insertSlides(text, id){
	slideid = slideid + 1;
	var pos = text.search(';');
	if(pos > 0){
		var slides = text.split(';');
		var tmp = [];
		for(var x in slides){
			if(slides[x].indexOf(':')>0){
				tmp.push(slides[x].trim());
			}
		}
		slides = tmp;
		var info = slides[0].split(':');
		var slideInfo = {cur:0, all:slides, imgs:[]};
		slideStore[slideid] = slideInfo;
		for(var x in slides){
			var localinfo = slides[x].split(':');
			var img = new Image();
			img.src = localinfo[0].trim() + '/' + localinfo[1].trim() + '.png';
			(()=>{
				const curid = slideid;
				img.onclick = ()=>{nextSlide(curid);}
			})();
			
			img.style = 'width:100%; position:relative; top:-10pt; left:0pt;';
			img.id = "slide_"+slideid;
			slideInfo.imgs.push(img);
		}
		
		var rv = "<div class='slideview' id='slideframe_"+slideid+"' style='color:rgb(50,50,50);'>"
		rv += "<img class='expandslide' id='expand_"+slideid+"' style='width:10pt;' onclick='growframe("+slideid+")' src='icons/grow.png' /><img id='slide_"+slideid+"' onclick='nextSlide("+slideid+")' style='width:100%; position:relative; top:-10pt; left:0pt;' src='"+info[0] + "/" + info[1]+".png'/>"
		rv += "<img onclick='nextSlide("+slideid+")' style='width:10pt;' src='icons/next.png' />"
		rv += "<img onclick='nextSlide("+slideid+")' id='bar_"+slideid+"' style='width:1%;height:10pt;' src='icons/bar.png' />"
		rv += "</div>"
		return rv;
		
	}else{
		var info = text.split(':');
		var rv = "<img class='slideview' src='"+info[0].trim() + "/" + info[1].trim() +".png'/>"
		return rv;
	}	
}

function codeblock(text, id){
	var info = text.split('\n');
	var rv = "<div class ='codeblock'><code>";
	for(var i in info){
		var line = info[i];
		line = line.replace("\t", "  ");		
		var pos = line.search(/\S/); 
		line = line.trim();		
		var chw = 10;
		if(window.screen.width < 700){
			chw = 7;			
		}
		if(pos >= 0){
			rv += "<div style='margin-left:" + pos * chw + "px;'>" + line + "</div>"
		}
	}
	rv += "</code></div>"
	return rv;
	
}

function asideformat(text, id){
	var info = text.split('\n');
	var rv = "<div class='aside'>";
	rv += text;
	rv += "</div>";
	return rv;
	
}


function processDocument(){
	footnotes = {};	
	loadAllFootnotes('biblio.bib', function(){
		processTag("grammar", gramarify);
		processTag("quote", quotify);
		processTag("rule", rulify);
		processTag("cite", citefy);
		processTag("slide", insertSlides);
		processTag("codeblock", codeblock);		
		processTag("jsexample", jsexamplify);
		processTag("footnotes", footrender);
		processTag("aside", asideformat);
	});
}