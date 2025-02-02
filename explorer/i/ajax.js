function g(sp,pubaddr,pubitem,loclen,locnum) {
  var p = sp.parentNode;
  var cl = p.childNodes;
  var note = cl[0];
  sp.onclick = "";
  var xhttp = new XMLHttpRequest();
  xhttp.onreadystatechange = function() { if (this.readyState == 4 && this.status == 200) { sp.innerHTML = this.responseText; } };
  xhttp.open('GET', "spajax.php?d=" + pubaddr + "&i=" + pubitem + "&l=" + loclen + "&n=" + locnum, true);
  xhttp.send();
}
