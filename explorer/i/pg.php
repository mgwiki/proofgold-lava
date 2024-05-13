<?php
ini_set('display_errors', 1);
ini_set('display_startup_errors', 1);
error_reporting(E_ALL);

function pgport($fnctn, $port, $loginpass) {
    $fp = fsockopen('127.0.0.1', $port);
    if (!$fp) { echo "ERROR: Could not establish connection to PG\n"; die(); }
    fputs($fp,$loginpass . "\n" . $fnctn . "\n");
    if (!$fp) { echo "ERROR: Failed to write request to PG\n"; die (); }
    $buffer = "";
    while(!feof($fp)) {
        if (is_resource($fp)) {
            $buffer .= fgets($fp, 4096);
        } else {
            echo "ERROR communicating with Proofgold\n"; die ();
        }
    }
    if (!fclose($fp)) { echo "ERROR: Failed to close connection to Proofgold\n"; die(); }
    return $buffer;
}

function pg($fnctn) {
    return pgport($fnctn, 21810, "Z-f9awzkEuVHWvqv\ncxuPnFJfYq+MmeaK");
}

function pgopen($fnctn) {
    return pgport($fnctn, 21818, "f9awzkEuVHWvqv-Z\nuPnFJfYq+MmeaKxc");
}

function pgj($fnctn) {
    $response = pg($fnctn);
    if (is_string($response)) {
        $decoded = json_decode($response);
        if (json_last_error() === JSON_ERROR_NONE) {
            return $decoded;
        } else { echo "ERROR: Failed to decode JSON response (".json_last_error_msg().")\n"; die(); }
    } else { echo "ERROR: Received invalid response from Proofgold\n"; die(); }
}

function ahref($item) {
  return ("<a href=\"q.php?b=" . $item . "\">". $item . "</a>");
}

function ahrefblock($item) {
  return ("<a href=\"Bl.php?b=" . $item . "\">". $item . "</a>");
}

function abbrv($item) {
  return ("<a href=\"q.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a>");
}

function abbrvblock($item) {
  return ("<a href=\"Bl.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a>");
}

function abbrvstx($item) {
  return ("<a href=\"STX.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a>");
}

function mglinki($item, $els) {
    return ((file_exists ("/home/cezary/mgw_test/etc/i/" . $item)) ? (file_get_contents("/home/cezary/mgw_test/etc/i/" . $item)) : $els);
}

function mglinka($item, $els) {
    return ((file_exists ("/home/cezary/mgw_test/etc/a/" . $item)) ? (file_get_contents("/home/cezary/mgw_test/etc/a/" . $item)) : $els);
}

function abbrvaddr($item) {
  return ("<a href=\"Ad.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a><sup>" . mglinka($item, "") . "</sup>");
}

function abbrvop($item) {
    return ("<a href=\"OP.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a><sup>" . mglinki($item, "") . "</sup>");
}

function abbrvname($item,$name) {
  return ("<a href=\"OP.php?b=" . $item . "\">" . $name . "</a><sup>" . mglinki($item, "") . "</sup>");
}

function abbrvasset1($item) {
  return ("<a href=\"As.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a>");
}

function abbrvasset($item,$itema) {
  return ("<a href=\"As.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a>/<a href=\"As.php?b=" . $itema . "\">" . substr($itema, 0, 5) . "..</a>");
}

function abbrvaddrasset($item,$itema) {
  return ("<a href=\"Ad.php?b=" . $item . "\">" . substr($item, 0, 5) . "..</a>/<a href=\"As.php?b=" . $itema . "\">" . substr($itema, 0, 5) . "..</a>");
}

function abbrvthyandname($o) {
    return ('<a href="theories.php?b=' . (isset($o->theory) ? $o->theory : "") . '">' . (isset($o->hfbuiltin) ? "hf axiom" : (isset($o->theory) ? $o->theorynames[0] : "empty theory")) . "</a>");
}

function nameordefault ($hex, $defaultnames) {
    if ($defaultnames == []) {
         return (abbrvop($hex));
    } else {
      	 return (abbrvname($hex, $defaultnames[0]));
    }
}
function doc($dc) {
    if (!(isset ($dc->defaultnames))) {
        $dc->defaultnames = [];
    }
    $output = '';
    if($dc->docitemcase == 'docknown') {
        $output .= "Known " . nameordefault($dc->propid,$dc->defaultnames) . " : ";
        $output .= ($dc->prop);
    } else if($dc->docitemcase == 'docdef') {
        $output .= "Definition " . nameordefault($dc->objid,$dc->defaultnames) . " := ";
        $output .= ($dc->def);
    } else if($dc->docitemcase == 'docpfof') {
        $output .= "Theorem " . nameordefault($dc->propid,$dc->defaultnames) . " : ";
        $output .= ($dc->prop . " (proof not displayed)");
    } else if ($dc->docitemcase == 'docparam') {
        $output .= "Param " . nameordefault($dc->objid,$dc->defaultnames) . " : ";
        $output .= ($dc->stp);
    } else  if($dc->docitemcase == 'docconj') {
        $output .= "Conjecture " . nameordefault($dc->propid,$dc->defaultnames) . " : ";
        $output .= ($dc->prop);
    } else {
        $output .= "Unknown Docitemcase ";
        $output .= item ("doc", $dc);
    }
    $output .= "<br/>";
    return $output;
}

function thyspec($dc) {
    if (!(isset ($dc->defaultnames))) {
        $dc->defaultnames = [];
    }
    $output = '';
    if($dc->theoryitemcase == 'thyaxiom') {
        $output .= "Axiom " . nameordefault($dc->propid, $dc->defaultnames) . " : " . $dc->prop;
    } else if($dc->theoryitemcase == 'thyprim') {
        $output .= "Prim " . nameordefault($dc->objid, ["Prim" . $dc->primnum]) . " : " . $dc->stp;
    } else if($dc->theoryitemcase == 'thydef') {
        $output .= "Def " . nameordefault($dc->objid, $dc->defaultnames) . " : " . $dc->stp . " := " . $dc->def;
    } else {
        $output .= "Unknown Thyitemcase " . $dc->theoryitemcase;
        var_export($dc);
    }
    $output .= "<br/>";
    return $output;
}

function preasset($v) {
    $output = '';
    $vp = $v->preasset;
    if ($vp->preassettype == 'currency') {
        $output .= number_format($vp->val->bars,2) . " bars";
    } else if ($vp->preassettype == 'bounty') {
        $output .= '<font color="red">BOUNTY</font> ' . number_format($vp->val->bars,2) . " bars";
    } else if ($vp->preassettype == 'ownsobj') {
        // objaddr ignored
        $output .= "ownership of " . abbrv($vp->objid) . " as obj with payaddr " . abbrvaddr($vp->owneraddress);
        if (isset($vp->royalty)) {
            $output .= " rightscost " . number_format($vp->royalty->bars, 2);
        } else {
            $output .= " no rights";
        }
    } else if ($vp->preassettype == 'ownsprop') {
        $output .= "ownership of " . abbrv($vp->propid) . " as prop with payaddr " . abbrv($vp->owneraddress);
        if (isset($vp->royalty)) {
            $output .= " rightscost " . number_format($vp->royalty->bars, 2);
        } else {
            $output .= " no rights";
        }
    } else if ($vp->preassettype == 'ownsnegprop') {
        $output .= "negprop ownership";
    } else if (($vp->preassettype == 'rightsobj') || ($vp->preassettype == 'marker') || ($vp->preassettype == 'rightsprop')) {
        $output .= $vp->preassettype;
    } else if ($vp->preassettype == 'doc') {
        $output .= "doc published by " . abbrvaddr($vp->publisher) . "<div align=left>";
        $doccount = count($vp->doc); // foreach but reversed
        while ($doccount) {
            $output .= doc($vp->doc[--$doccount]);
        }
        $output .= "</div>";
    } else if ($vp->preassettype == 'theoryspec') {
        $output .= "theory published by " . abbrvaddr($vp->publisher) . "<div align=left>";
        foreach ($vp->theoryspec as $vt) {
            $output .= thyspec($vt);
        }
        $output .= "</div>";
    } else {
        $output .= "Unknown preassettype:" . $vp->preassettype;
        var_export($vp);
    }
    if (isset($v->obligation)) {
        $output .= " controlledby " . abbrvaddr($v->obligation->lockaddress) . " upto " . $v->obligation->lockheight;
        unset ($v->obligation);
    }
    return $output;
}

function oneasset($v) {
  $output = abbrvasset($v->assethash, $v->assetid) . " bday: " . ahrefblock($v->bday) . " " . preasset($v) . "<br/>";
  return $output;
}

function onevout($vo) {
    $output = abbrvaddrasset($vo->address, $vo->assetid) . " " . preasset($vo) . "</br>";
    return $output;
}

?>
