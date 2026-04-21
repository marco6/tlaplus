/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.value;

import java.util.Objects;

import tlc2.pprint.PrettyPrint;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.Assert;
import util.UniqueString;

public abstract class Values {

	private static int WIDTH = Integer.getInteger(Values.class.getName() + ".width", 80);

	public static String ppr(String s) {
		return PrettyPrint.mypp(s, WIDTH);
	}

	public static String ppr(IValue v) {
		if (v == null) {
			return "null";
		}
		return PrettyPrint.mypp(v.toString(), WIDTH);
	}

	public static boolean equals(Value a, Value b) {
		return a == b || a != null && a.equals(b);
	}

	public static boolean equals(Value a, boolean b) {
		return a instanceof BoolValue && ((BoolValue) a).val == b;
	}

	public static boolean equals(Value a, int b) {
		return a instanceof IntValue && ((IntValue) a).val == b;
	}

	public static boolean equals(boolean a, Value b) {
		return b instanceof BoolValue && ((BoolValue) b).val == a;
	}

	public static boolean equals(int a, Value b) {
		return b instanceof IntValue && ((IntValue) b).val == a;
	}

	public static Value select(Value arg, int uid) {
		if (arg instanceof RecordValue) {
			var record = (RecordValue) arg;
			int rlen = record.names.length;
			for (int i = 0; i < rlen; i++) {
				if (record.names[i].getTok() == uid) {
					return record.values[i];
				}
			}
			return null;

		} else {
			FcnRcdValue fcn = (FcnRcdValue) arg.toFcnRcd();
			var sval = new StringValue(UniqueString.uidToUniqueString(uid));
			if (fcn == null) {
				Assert.fail("Attempted to select field " + sval + " from a non-record" +
						" value " + Values.ppr(arg.toString()) + "\n");
			}
			return fcn.apply(sval, 0);
		}
	}
}
