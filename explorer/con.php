<html>
<head>
  <link rel="stylesheet" href="chat5.css">
  <script src="https://cdn.plot.ly/plotly-latest.min.js"></script>
  <script src="https://unpkg.com/d3"></script>
  <script src="https://unpkg.com/sunburst-chart"></script>
  <script src="https://cdnjs.cloudflare.com/ajax/libs/PapaParse/5.3.0/papaparse.min.js"></script>
</head>
<body>
<?php include 'pg-include.php'; ?>

<center>
<form action="q.php" method="GET"><font size=-3>Search for blocks/addresses/... <input type="text" name="b" placeholder="Search.."></font>
<input type="submit" value="Go!" /></form>
<h1>Proofgold connections</h1>
<hr/>
<div id="chart"></div>

<script>
    const color = d3.scaleOrdinal(d3.schemePaired);
    fetch('con.json').then(res => res.json()).then(data => {
      Sunburst()
        .data(data)
        .label('name')
        .size('size')
        .color((d, parent) => color(parent ? parent.data.name : null))
        .tooltipContent((d, node) => `Size: <i>${node.value}</i>`)
        (document.getElementById('chart'));
    });
</script>

</body></html>
