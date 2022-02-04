import json
import pandas as pd
from multicorn import ForeignDataWrapper

df = pd.DataFrame({
    "number": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    "parity": ["even", "odd", "even", "odd", "even", "odd", "even", "odd", "even", "odd"]
})

def fake_remote_pandas_endpoint(columns=None, aggs=None, group_clauses=None):
    if group_clauses is not None:
        return df.groupby(group_clauses, as_index=False).agg(aggs).to_dict('records')
    if aggs is not None:
        # Returns {"column_1": {"avg": x, "sum": y}, "column_2": {"min": z}, ..}
        return df.agg(aggs).to_dict()

    return df[columns].to_dict("records")

_PG_TO_PANDAS_FUNC_MAP = {
    "min": "min",
    "max": "max",
    "sum": "sum",
    "avg": "average",
    "count": "count",
}

def _convert_aggs_arg(aggs):
    # Convert aggs in accordance with Pandas API:
    # {"column_1": ["avg", "sum"], "column_2": ["min"], ..}
    pandas_aggs = {}
    for agg_props in aggs.values():
        function_name = _PG_TO_PANDAS_FUNC_MAP[agg_props["function"]]

        if agg_props["column"] not in pandas_aggs:
            pandas_aggs[agg_props["column"]] = [function_name]
        else:
            pandas_aggs[agg_props["column"]].append(function_name)
    return pandas_aggs


class PandasFdw(ForeignDataWrapper):

    def can_pushdown_upperrel(self):
        return {
            "groupby_supported": True,
            "agg_functions": list(_PG_TO_PANDAS_FUNC_MAP)
        }

    def explain(self, quals, columns, aggs=None, group_clauses=None, verbose=False):
        return [
            f"quals: {quals}",
            f"columns: {columns}",
            f"aggs: {json.dumps(aggs, indent=4)}",
            f"group_clauses: {group_clauses}"
        ]

    def execute(self, quals, columns, aggs=None, group_clauses=None):
        if group_clauses is not None:
            pandas_aggs = _convert_aggs_arg(aggs)

            for row in fake_remote_pandas_endpoint(columns, pandas_aggs, group_clauses):
                # Convert result back to Multicorn API:
                # {"column_1.avg": x, "column_1.sum": y, "column2": z, ...}
                result = {}
                for agg_name, agg_props in aggs.items():
                    function_name = _PG_TO_PANDAS_FUNC_MAP[agg_props["function"]]
                    result[agg_name] = row[(agg_props["column"], function_name)]

                for group_clause in group_clauses:
                    result[group_clause] = row[(group_clause, "")]

                yield result
        elif aggs is not None:
            pandas_aggs = _convert_aggs_arg(aggs)
            row = fake_remote_pandas_endpoint(columns, pandas_aggs)

            # Convert result back to Multicorn API:
            # {"column_1.avg": x, "column_1.sum": y, "column_2.min": z, ...}
            result = {}
            for agg_name, agg_props in aggs.items():
                function_name = _PG_TO_PANDAS_FUNC_MAP[agg_props["function"]]
                result[agg_name] = row[agg_props["column"]][function_name]

            yield result
        else:
            for row in fake_remote_pandas_endpoint(columns):
                yield row
        return
