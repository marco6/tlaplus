package tlc2.util;

import java.io.IOException;

import com.google.gson.stream.JsonWriter;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.value.ValueConstants;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.MethodValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.OpLambdaValue;
import tlc2.value.impl.OpRcdValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetCapValue;
import tlc2.value.impl.SetCupValue;
import tlc2.value.impl.SetDiffValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.SetOfTuplesValue;
import tlc2.value.impl.SetPredValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.SubsetValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.UnionValue;
import tlc2.value.impl.UserValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * Writes the given state in JSON format.
 * 
 * @see https://www.json.org/json-en.html
 * 
 * 
 */
public class GraphStateWriter extends StateWriter {
	// Include states in the dot file that are excluded from the model via a state
	// or action constraint.
	private final boolean constrained;

	// Determines whether or not stuttering edges should be rendered.
	private final boolean stuttering;

	public GraphStateWriter(final String fname,
			final boolean constrained, final boolean stuttering) throws IOException {
		super(fname);
		this.constrained = constrained;
		this.stuttering = stuttering;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see tlc2.util.IStateWriter#isDot()
	 */
	@Override
	public boolean isDot() {
		return false;
	}

	public boolean isConstrained() {
		return this.constrained;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState)
	 */
	public synchronized void writeState(final TLCState state) {
		writeState(state, false);
	}

	private void writeState(final TLCState state, final boolean constrained) {
		if (constrained) {
			this.writer.append("C ");
		} else {
			this.writer.append("S ");
		}
		this.writer.append(Long.toString(state.fingerPrint())).append(' ');
		JsonWriter jsonWriter = new JsonWriter(this.writer);
		try {
			serializeState(jsonWriter, state);
			jsonWriter.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
		this.writer.append("\n");
	}

	private void serializeState(final JsonWriter writer, final TLCState state) throws IOException {
		writer.beginObject();
		OpDeclNode[] vars = state.getVars();
		for (var var : vars) {
			UniqueString key = var.getName();
			if (key.toString().equals("action") || key.toString().equals("zaction")) {
				continue;
			}
			writer.name(key.toString());
			var val = (Value) state.lookup(key);
			serializeValue(writer, val);
		}
		writer.endObject();
	}

	private void serializeValue(final JsonWriter writer, final Value val) throws IOException {
		if (val == null) {
			writer.nullValue();
			return;
		}

		switch (val.getKind()) {
			case ValueConstants.BOOLVALUE:
				var boolVal = (BoolValue) val;
				writer.value(boolVal.val);
				break;
			case ValueConstants.INTVALUE:
				var intVal = (IntValue) val;
				writer.value(intVal.val);
				break;
			case ValueConstants.REALVALUE:
				writer.value(0.0);
				break;
			case ValueConstants.STRINGVALUE:
				var strVal = (StringValue) val;
				writer.value(strVal.val.toString());
				break;
			case ValueConstants.RECORDVALUE:
				var recordVal = (RecordValue) val;
				writer.beginObject();
				for (int i = 0; i < recordVal.names.length; i++) {
					writer.name(recordVal.names[i].toString());
					serializeValue(writer, (Value) recordVal.values[i]);
				}
				writer.endObject();
				break;
			case ValueConstants.SETENUMVALUE:
				writer.beginArray();
				var setEnumVal = (SetEnumValue) val;
				for (int i = 0; i < setEnumVal.elems.size(); i++) {
					serializeValue(writer, setEnumVal.elems.elementAt(i));
				}
				writer.endArray();
				break;
			case ValueConstants.SETPREDVALUE:
				var setPredVal = (SetPredValue) val;
				serializeValue(writer, setPredVal.toSetEnum());
				break;
			case ValueConstants.TUPLEVALUE:
				var tupleVal = (TupleValue) val;
				writer.beginArray();
				for (int i = 0; i < tupleVal.elems.length; i++) {
					serializeValue(writer, (Value) tupleVal.elems[i]);
				}
				writer.endArray();
				break;
			case ValueConstants.FCNLAMBDAVALUE:
				var fcnLambdaVal = (FcnLambdaValue) val;
				serializeValue(writer, fcnLambdaVal.toFcnRcd());
				break;
			case ValueConstants.FCNRCDVALUE:
				var fcnRcdVal = (FcnRcdValue) val;
				if (fcnRcdVal.size() == 0) {
					writer.beginArray();
					writer.endArray();
				} else if (fcnRcdVal.isRcd()) {
					writer.beginObject();
					for (int i = 0; i < fcnRcdVal.domain.length; i++) {
						writer.beginObject();
						writer.name(((StringValue) fcnRcdVal.domain[i]).val.toString());
						serializeValue(writer, (Value) fcnRcdVal.values[i]);
						writer.endObject();
					}
					writer.endObject();
				} else if (fcnRcdVal.isTuple()) {
					writer.beginArray();
					for (int i = 0; i < fcnRcdVal.values.length; i++) {
						serializeValue(writer, (Value) fcnRcdVal.values[i]);
					}
					writer.endArray();
				} else {
					var domain = fcnRcdVal.getDomainAsValues();
					writer.beginArray();
					for (int i = 0; i < fcnRcdVal.values.length; i++) {
						writer.beginArray();
						serializeValue(writer, domain[i]);
						serializeValue(writer, (Value) fcnRcdVal.values[i]);
						writer.endArray();
					}
					writer.endArray();
				}
				break;
			case ValueConstants.OPLAMBDAVALUE:
				var opLambdaVal = (OpLambdaValue) val;
				writer.beginObject();
				writer.name("$operator");
				writer.value(opLambdaVal.opDef.getName().toString());
				writer.endObject();
				break;
			case ValueConstants.OPRCDVALUE:
				var opRcdVal = (OpRcdValue) val;
				writer.beginArray();
				for (int i = 0; i < opRcdVal.size(); i++) {
					var domain = opRcdVal.domain.elementAt(i);
					writer.beginArray();
					for (var d : domain) {
						serializeValue(writer, (Value) d);
					}
					writer.endArray();
					serializeValue(writer, (Value) opRcdVal.values.elementAt(i));
				}
				writer.endArray();
				break;
			case ValueConstants.METHODVALUE:
				var methodVal = (MethodValue) val;
				writer.beginObject();
				writer.name("$method");
				writer.value(methodVal.getMethodName());
				writer.endObject();
				break;
			case ValueConstants.SETOFFCNSVALUE:
				serializeSetOfFcnsValue(writer, (SetOfFcnsValue) val);
				break;
			case ValueConstants.SETOFRCDSVALUE:
				var setOfRcdsVal = (SetOfRcdsValue) val;
				serializeSetOfRcdsValue(writer, setOfRcdsVal);
				break;
			case ValueConstants.SETOFTUPLESVALUE:
				serializeSetOfTuplesValue(writer, (SetOfTuplesValue) val);
				break;
			case ValueConstants.SUBSETVALUE:
				var subsetVal = (SubsetValue) val;
				serializeValue(writer, subsetVal.toSetEnum());
				break;
			case ValueConstants.SETDIFFVALUE:
				var setDiffVal = (SetDiffValue) val;
				serializeValue(writer, setDiffVal.toSetEnum());
				break;
			case ValueConstants.SETCAPVALUE:
				var setCapVal = (SetCapValue) val;
				serializeValue(writer, setCapVal.toSetEnum());
				break;
			case ValueConstants.SETCUPVALUE:
				var setCupVal = (SetCupValue) val;
				serializeValue(writer, setCupVal.toSetEnum());
				break;
			case ValueConstants.UNIONVALUE:
				var unionVal = (UnionValue) val;
				serializeValue(writer, unionVal.toSetEnum());
				break;
			case ValueConstants.MODELVALUE:
				var modelVal = (ModelValue) val;
				writer.beginObject();
				writer.name("$value");
				writer.value(modelVal.val.toString());
				writer.endObject();
				break;
			case ValueConstants.USERVALUE:
				var userVal = (UserValue) val;
				writer.beginObject();
				writer.name("$userValue");
				writer.value(userVal.userObj.toString());
				writer.endObject();
				break;
			case ValueConstants.INTERVALVALUE:
				var intervalVal = (IntervalValue) val;
				writer.beginObject();
				writer.name("").value(intervalVal.low);
				writer.name("").value(intervalVal.high);
				writer.endObject();
				break;
			case ValueConstants.UNDEFVALUE:
				writer.nullValue();
				break;
			case ValueConstants.LAZYVALUE:
				var value = ((LazyValue) val);
				serializeValue(writer, value.getUnchecked());
				break;
			case ValueConstants.DUMMYVALUE:
				writer.nullValue();
				break;
		}
	}

	private void serializeSetOfRcdsValue(JsonWriter writer, SetOfRcdsValue val) throws IOException {
		boolean unlazy = true;
		long sz = 1;
		for (int i = 0; i < val.values.length; i++) {
			sz *= val.values[i].size();
			if (sz < -2147483648 || sz > 2147483647) {
				unlazy = false;
				break;
			}
		}
		unlazy = sz < TLCGlobals.enumBound;
		if (unlazy) {
			serializeValue(writer, val.toSetEnum());
		} else {
			writer.beginObject();
			for (int i = 0; i < val.values.length; i++) {
				writer.name(val.names[i].toString());
				serializeValue(writer, (Value) val.values[i]);
			}
			writer.endObject();
		}
	}

	private void serializeSetOfTuplesValue(JsonWriter writer, SetOfTuplesValue val) throws IOException {
		boolean unlazy = true;
		long sz = 1;
		for (int i = 0; i < val.sets.length; i++) {
			sz *= val.sets[i].size();
			if (sz < -2147483648 || sz > 2147483647) {
				unlazy = false;
				break;
			}
		}
		unlazy = sz < TLCGlobals.enumBound;

		if (unlazy) {
			serializeValue(writer, val.toSetEnum());
		} else {
			writer.beginObject();
			writer.name("$tuples");
			writer.beginArray();
			for (int i = 0; i < val.sets.length; i++) {
				serializeValue(writer, val.sets[i]);
			}
			writer.endArray();
			writer.endObject();
		}
	}

	private void serializeSetOfFcnsValue(final JsonWriter writer, final SetOfFcnsValue val) throws IOException {
		boolean unlazy = true;
		long sz = 1;
		int dsz = val.domain.size();
		int rsz = val.range.size();
		for (int i = 0; i < dsz; i++) {
			sz *= rsz;
			if (sz < -2147483648 || sz > 2147483647) {
				unlazy = false;
				break;
			}
		}
		unlazy = sz < TLCGlobals.enumBound;

		if (unlazy) {
			serializeValue(writer, val.toSetEnum());
		} else {
			writer.beginObject();
			writer.name("$domain");
			serializeValue(writer, val.domain);
			writer.name("$range");
			serializeValue(writer, val.range);
			writer.endObject();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState,
	 * boolean)
	 */
	public void writeState(TLCState state, TLCState successor, short stateFlags) {
		writeState(state, successor, stateFlags, Visualization.DEFAULT);
	}

	public void writeState(final TLCState state, final TLCState successor, final short stateFlags, Action action) {
		writeState(state, successor, null, 0, 0, stateFlags, Visualization.DEFAULT, action, null);
	}

	public void writeState(final TLCState state, final TLCState successor, final short stateFlags, Action action,
			SemanticNode pred) {
		writeState(state, successor, null, 0, 0, stateFlags, Visualization.DEFAULT, action, pred);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState,
	 * boolean, tlc2.util.IStateWriter.Visualization)
	 */
	public void writeState(TLCState state, TLCState successor, short stateFlags, Visualization visualization) {
		writeState(state, successor, null, 0, 0, stateFlags, visualization, null, null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState,
	 * tlc2.util.BitVector, int, int, boolean)
	 */
	public void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int length,
			short stateFlags) {
		writeState(state, successor, actionChecks, from, length, stateFlags, Visualization.DEFAULT, null, null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState, tlc2.tool.TLCState,
	 * java.lang.String, boolean, tlc2.util.IStateWriter.Visualization)
	 */
	private synchronized void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from,
			int length, short stateFlags,
			Visualization visualization, Action action, SemanticNode pred) {
		if (!stuttering && visualization == Visualization.STUTTERING) {
			// Do not render stuttering transitions unless requested.
			return;
		}

		if (!isSet(stateFlags, IStateWriter.IsSeen)) {
			this.writeState(successor, isSet(stateFlags, IStateWriter.IsNotInModel));
		}

		final long sfp = successor.fingerPrint();
		final long cfp = state.fingerPrint();

		this.writer.append("A ");
		this.writer.append(Long.toString(cfp));
		this.writer.append(' ');
		this.writer.append(Long.toString(sfp));

		var actionValue = successor.lookup("action");
		if (actionValue == null) {
			actionValue = successor.lookup("zaction");
		}
		if (actionValue instanceof RecordValue) {
			RecordValue actionRecord = (RecordValue) actionValue;
			assert actionRecord.names.length == 1;
			this.writer.append(' ');
			this.writer.append(actionRecord.names[0].toString());
			this.writer.append(' ');
			var jsonWriter = new JsonWriter(this.writer);
			try {
				serializeValue(jsonWriter, actionRecord.values[0]);
				jsonWriter.flush();
			} catch (IOException e) {
				e.printStackTrace();
			}
			this.writer.append('\n');
			this.writer.flush();
		}
	}
}
