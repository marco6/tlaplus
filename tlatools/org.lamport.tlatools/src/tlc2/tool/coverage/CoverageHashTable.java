/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package tlc2.tool.coverage;

import java.util.Set;

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import tla2sany.explorer.ExploreNode;
import tla2sany.semantic.OpDefNode;

@SuppressWarnings("serial")
class CoverageHashTable extends Int2ObjectOpenHashMap<ExploreNode> {
	private final Set<OpDefNode> nodes;

	public CoverageHashTable(final Set<OpDefNode> nodes) {
		this.nodes = nodes;
	}

	@Override
	public ExploreNode putIfAbsent(int key, ExploreNode value) {
		if (value instanceof OpDefNode) {
			final OpDefNode odn = (OpDefNode) value;
			if (odn.getInRecursive()) {
				if (nodes.contains(odn)) {
					// RECURSIVE operators
					return super.putIfAbsent(key, value);
				}
			}
		}
		return null;
	}
}